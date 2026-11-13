import Compiler.SolidityImport.ExprHelpers
import Compiler.SolidityImport.AbiLowering
import Verity.Core.Model.ECM

/-! ABI-v1 calldata and straight-line scratch memory for Solidity 0.7.6.
Writes stay at the free-memory pointer or a bounded constant displacement from
it. This cannot overwrite existing Solidity allocations or allocator metadata.
The pointer itself is not advanced: later Solidity allocation may reuse it. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyMemory
open Lean

/-- ABI-v1 scalar cleanup occurs when loading an external argument. -/
def cleanScalar (ty : ParamType) (word : Expr) : Expr :=
  match ty with
  | .uint8 => .bitAnd word (.literal (2^8-1))
  | .uint16 => .bitAnd word (.literal (2^16-1))
  | .uintN bits => if bits < 256 then .bitAnd word (.literal (2^bits-1)) else word
  | .intN bits =>
      if 0 < bits && bits < 256 && bits % 8 == 0 then
        .signextend (.literal (bits / 8 - 1)) word else word
  | .address => .bitAnd word (.literal (2^160-1))
  | .bool => .logicalNot (.logicalNot word)
  | _ => word

/-- Legacy enum cleanup is a use-site INVALID check, not an ABI-v1 entry check. -/
def checkedEnum (at_ : Json) (ty : String) (value : Val) : M Val := do
  let members ← resolveEnumMembers at_ ty
  let value ← atom value
  return { value with pre := value.pre.push (.ite
    (.lt value.expr (.literal members.size)) []
    [.ecm Compiler.ECM.SolidityInvalid.module []]) }

/-- Legacy calldata bytes have inclusive 32-bit bounds and no memory allocation. -/
def calldataHead (offset header length data : String) (words headOffset : Nat) : List Stmt :=
  let guard := AbiLowering.guard
  [ guard (.ge .calldatasize (.literal (4 + 32*words)))
  , .letVar offset (.calldataload (.literal headOffset))
  , guard (.le (.localVar offset) (.literal (2^32)))
  , .letVar header (.add (.literal 4) (.localVar offset))
  , guard (.le (.add (.localVar header) (.literal 32)) .calldatasize)
  , .letVar length (.calldataload (.localVar header))
  , .letVar data (.add (.localVar header) (.literal 32))
  , guard (.le (.localVar length) (.literal (2^32)))
  , guard (.le (.add (.localVar data) (.localVar length)) .calldatasize) ]

private partial def calls (node : Json) (names : Array String) : Bool :=
  match node with
  | .arr xs => xs.any (calls · names)
  | .obj fields =>
      ((optStr node "nodeType" == some "YulFunctionCall") &&
        ((field? node "functionName").bind (optStr · "name")).any names.contains) ||
      fields.toList.any (fun (_, child) => calls child names)
  | _ => false

/-- Keep terminal-revert lowering separate from the scratch-memory continuation. -/
def applies (node : Json) : Bool :=
  calls node #["mstore", "calldatacopy", "keccak256"] && !calls node #["revert"]

/-- No control flow, external effects, pointer assignment, or hidden Yul functions. -/
partial def validate (node : Json) : M Unit := do
  match node with
  | .arr xs => xs.forM validate
  | .obj fields =>
      if let some kind := optStr node "nodeType" then
        unless #["YulBlock", "YulVariableDeclaration", "YulTypedName", "YulLiteral",
            "YulIdentifier", "YulFunctionCall", "YulAssignment",
            "YulExpressionStatement"].contains kind do
          failAt node "Solidity 0.7.6 scratch memory requires straight-line assembly"
        if kind == "YulFunctionCall" then
          let name := (field? node "functionName").bind (optStr · "name")
          unless name.any (#["mload", "mstore", "calldatacopy", "keccak256", "add",
              "sub", "mul", "and", "byte", "chainid"].contains ·) do
            failAt node "unsupported Solidity 0.7.6 scratch-memory builtin"
      for (_, child) in fields do validate child
  | _ => pure ()

private def number? (node : Json) : Option Nat := do
  guard (optStr node "nodeType" == some "YulLiteral")
  guard (optStr node "kind" == some "number")
  let value ← optStr node "value"
  Compiler.Hex.parseHexNat? value <|> value.toNat?

/-- Static displacement from an allocator-pointer snapshot. No variable offsets. -/
private partial def displacement? (node : Json)
    (pointers : RBMap String Nat compare) : Option Nat := do
  if optStr node "nodeType" == some "YulIdentifier" then
    return ← pointers.find? (← optStr node "name")
  guard (optStr node "nodeType" == some "YulFunctionCall")
  let name ← (field? node "functionName").bind (optStr · "name")
  let args ← (field? node "arguments").bind (·.getArr?.toOption)
  if name == "mload" && args.size == 1 && number? args[0]! == some 64 then return 0
  guard (name == "add" && args.size == 2)
  let offset ← ((do return (← displacement? args[0]! pointers) + (← number? args[1]!))
    <|> (do return (← number? args[0]!) + (← displacement? args[1]! pointers)))
  guard (offset ≤ 2^32)
  return offset

private def checkAddress (node : Json) (pointers : RBMap String Nat compare) : M Unit := do
  unless (displacement? node pointers).isSome do
    failAt node "legacy scratch memory requires a free-pointer root and constant displacement"

private partial def expression (node : Json) (refs : Array Json)
    (pointers : RBMap String Nat compare) (leaf : Json → M Val) : M Expr := do
  if optStr node "nodeType" == some "YulIdentifier" then
    let src ← mStr (← mField node "src")
    if let some ref := refs.find? (fun ref => optStr ref "src" == some src) then
      if let some suffix := optStr ref "suffix" then
        let id ← mNat (← mField ref "declaration")
        let some cb := (← get).calldataBytes.find? id
          | failAt node "unresolved calldata assembly reference"
        unless !cb.inMemory && (suffix == "offset" || suffix == "length") do
          failAt node "legacy assembly accepts only calldata bytes offset/length suffixes"
        return .localVar (if suffix == "offset" then cb.dataBinding else cb.lengthBinding)
  if optStr node "nodeType" != some "YulFunctionCall" then
    let value ← leaf node
    unless value.pre.isEmpty do failAt node "effectful scratch-memory operand"
    return value.expr
  let name ← mStr (← mField (← mField node "functionName") "name")
  let args ← mArr (← mField node "arguments")
  if name == "mload" && args.size == 1 then
    if number? args[0]! != some 64 then checkAddress args[0]! pointers
    return .mload (← expression args[0]! refs pointers leaf)
  if name == "keccak256" && args.size == 2 then checkAddress args[0]! pointers
  let xs ← args.mapM (expression · refs pointers leaf)
  match name, xs with
  | "add", #[a, b] => return .add a b
  | "sub", #[a, b] => return .sub a b
  | "mul", #[a, b] => return .mul a b
  | "and", #[a, b] => return .bitAnd a b
  | "byte", #[a, b] => return .byte a b
  | "chainid", #[] => return .chainid
  | "keccak256", #[a, b] => return .keccak256 a b
  | _, _ => failAt node "unsupported legacy scratch-memory expression or arity"

/-- Copy each source byte into physical memory, preserving the other 31 bytes
of the destination word. Explicit size/overflow tests zero-extend calldata;
selector bytes use their separate four-byte representation in Denote. -/
private def copyCalldata (destination source count : Expr) : M (Array Stmt) := do
  let dest ← atom { pre := #[], expr := destination }
  let src ← atom { pre := #[], expr := source }
  let size ← atom { pre := #[], expr := count }
  let index ← fresh
  let input ← fresh
  let output ← fresh
  let value ← fresh
  let offset := Expr.localVar input
  let byteValue := Expr.localVar value
  let target := Expr.localVar output
  let readByte := Stmt.ite (.lt offset (.literal 4))
    [.assignVar value (.byte offset (.calldataload (.literal 0)))]
    [.assignVar value (.byte (.literal 0) (.calldataload offset))]
  let body := [
    Stmt.letVar input (.add src.expr (.localVar index)),
    .letVar output (.add dest.expr (.localVar index)),
    .letVar value (.literal 0),
    .ite (.ge offset src.expr) [.ite (.lt offset .calldatasize) [readByte] []] [],
    .mstore target (.bitOr (.shl (.literal 248) byteValue)
      (.bitAnd (.mload target) (.literal (2^248-1))))]
  return dest.pre ++ src.pre ++ size.pre |>.push (.forEach index size.expr body)

/-- Materialize a validated calldata region for a legacy memory helper argument.
The allocator advances before the copy; an unaligned zero word clears the tail
and the next 32 bytes exactly as the ABI-v1 compiler does. -/
def materializeBytes (source length : Expr) : M EncodedBytes := do
  let pointer ← fresh
  let data := Expr.add (.localVar pointer) (.literal 32)
  let rounded := Expr.bitAnd (.add length (.literal 31)) (.bitNot (.literal 31))
  let copy ← copyCalldata data source length
  modify fun e => { e with encodingMemory := true }
  return {
    pre := #[.letVar pointer (.mload (.literal 64)),
      .mstore (.literal 64) (.add data rounded),
      .mstore (.localVar pointer) length] ++ copy ++
      #[.mstore (.add data length) (.literal 0)]
    pointer := data
    size := length }

/-- Lower byte-exact copies, physical memory reads/writes and hashes in source order.
Only Yul-local pointer snapshots may address the temporary region; external
assignment targets still pass the importer's declaration/type checks. -/
def lower (assembly : Json) (stmts refs : Array Json) (leaf : Json → M Val)
    (assign : Json → Json → Val → M Stmt) : M (Array Stmt) := do
  let mut pointers : RBMap String Nat compare := RBMap.empty
  let mut locals : RBMap String String compare := RBMap.empty
  let mut out := #[]
  for stmt in stmts do
    match ← mKind stmt with
    | "YulVariableDeclaration" | "YulAssignment" =>
        let declaration := optStr stmt "nodeType" == some "YulVariableDeclaration"
        let targets ← mArr (← mField stmt (if declaration then "variables" else "variableNames"))
        unless targets.size == 1 do failAt stmt "scratch memory requires one assignment target"
        let target := targets[0]!
        let name ← mStr (← mField target "name")
        let valueNode ← mField stmt "value"
        let value ← expression valueNode refs pointers leaf
        let displacement := displacement? valueNode pointers
        if declaration then
          unless optStr target "type" == some "" && !locals.contains name do
            failAt target "duplicate or typed scratch-memory local"
          let binding ← freshFor name
          out := out.push (.letVar binding value)
          locals := locals.insert name binding
          modify fun e => { e with yulNames := e.yulNames.insert name (.localVar binding) }
        else if let some binding := locals.find? name then
          out := out.push (.assignVar binding value)
        else
          out := out.push (← assign stmt target { pre := #[], expr := value })
        pointers := match displacement with
          | some offset => if locals.contains name then pointers.insert name offset else pointers
          | none => pointers.erase name
    | "YulExpressionStatement" =>
        let call ← mField stmt "expression"
        let name ← mStr (← mField (← mField call "functionName") "name")
        let args ← mArr (← mField call "arguments")
        unless (name == "mstore" && args.size == 2) ||
            (name == "calldatacopy" && args.size == 3) do
          failAt stmt "unsupported legacy scratch-memory statement or arity"
        checkAddress args[0]! pointers
        let xs ← args.mapM (expression · refs pointers leaf)
        if name == "mstore" then
          out := out.push (.mstore (xs.getD 0 (.literal 0)) (xs.getD 1 (.literal 0)))
        else
          let destination := xs.getD 0 (.literal 0)
          let source := xs.getD 1 (.literal 0)
          let count := xs.getD 2 (.literal 0)
          out := out ++ (← copyCalldata destination source count)
    | _ => failAt assembly "legacy scratch memory requires straight-line assembly"
  return out

end Compiler.CompilationModel.SolidityImport.LegacyMemory
