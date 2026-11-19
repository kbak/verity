import Compiler.SolidityImport.LegacyAbi
import Compiler.SolidityImport.LegacyBytePointers

/-! Legacy low-level CALL and STATICCALL return an explicit success flag and a memory
bytes buffer. Source checks and ABI decoding remain ordinary later statements. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyCallTuples
open Lean

/-- Match the resolved address builtin; a user-defined member can have the same name. -/
private def builtinMember (member : Json) (name : String) : Bool :=
  optStr member "nodeType" == some "MemberAccess" && optStr member "memberName" == some name &&
    (field? member "referencedDeclaration").isNone

/-- Static tuples, including their existing located rejection of call options. -/
def isStaticCall (node : Json) : Bool :=
  let init := (field? node "initialValue").getD Json.null
  let callee := (field? init "expression").getD Json.null
  let member := if optStr callee "nodeType" == some "FunctionCallOptions" then
    (field? callee "expression").getD Json.null else callee
  optStr init "nodeType" == some "FunctionCall" && builtinMember member "staticcall"

/-- A value-free CALL with one directly selector-encoded input. -/
def isSelectorCall (node : Json) : Bool :=
  let init := (field? node "initialValue").getD Json.null
  let callee := (field? init "expression").getD Json.null
  let args := ((field? init "arguments").bind (·.getArr?.toOption)).getD #[]
  optStr init "kind" == some "functionCall" && builtinMember callee "call" &&
    args.size == 1 && LegacyAbi.isSelectorEncoding args[0]!

/-- solc copies the encoded bytes to the free pointer for CALL, without advancing it.
The last four bytes share a word with live scratch bytes, including on empty responses. -/
private def selectorCallInput (node : Json) (input : EncodedBytes) : M EncodedBytes := do
  let .literal size := input.size | failAt node "expected a static selector encoding"
  let scratchName ← fresh
  let scratch := Expr.localVar scratchName
  let mut pre := input.pre.push (.letVar scratchName (.mload (.literal 64)))
  for i in [:size / 32] do
    let offset := Expr.literal (32 * i)
    pre := pre.push (.mstore (.add scratch offset) (.mload (.add input.pointer offset)))
  let tailOffset := Expr.literal (size - 4)
  let tailAddr := Expr.add scratch tailOffset
  let mask := Expr.literal (2^224 - 1)
  let high := Expr.bitAnd (.mload (.add input.pointer tailOffset)) (.bitNot mask)
  pre := pre.push (.mstore tailAddr (.bitOr high (.bitAnd (.mload tailAddr) mask)))
  return { input with pre, pointer := scratch }

/-- Evaluate operands without effects, retain all returndata and use the legacy
zero-slot pointer for empty responses. Nonempty responses allocate rounded space
at the current (possibly unaligned) free pointer, without clearing trailing bytes. -/
def lower (node : Json) (leaf : Json → M Val) (bytes : Json → M EncodedBytes) :
    M (Array Stmt) := do
  let isStatic := isStaticCall node
  let label := if isStatic then "raw static" else "selector"
  unless isStatic || isSelectorCall node do failAt node "expected a low-level call tuple"
  unless (← get).legacyWrapping do failAt node s!"{label} tuples require Solidity 0.7.6"
  if (← get).legacyAbiV2Files.contains (← get).currentFile then
    failAt node s!"{label} tuples require ABI coder v1"
  let init ← mField node "initialValue"
  let member ← mField init "expression"
  unless optStr member "nodeType" == some "MemberAccess" do
    failAt member "raw static call options are outside this slice"
  let base ← mField member "expression"
  unless ["address", "address payable"].contains (← mType base) do
    failAt base s!"{label} call requires an address receiver"
  let clean := fun arg => do
    let value ← leaf arg
    unless value.pre.isEmpty do failAt arg s!"{label} operands must be effect-free"
    pure value
  let target ← atom (← clean base)
  let arguments ← mArr (← mField init "arguments")
  let names ← mArr (← mField init "names")
  unless arguments.size == 1 && names.isEmpty do
    failAt init s!"{label} call requires one unnamed bytes argument"
  let input ← if LegacyAbi.isSelectorEncoding arguments[0]! then
    let encoded ← LegacyAbi.lower arguments[0]! clean
    if isStatic then pure encoded else selectorCallInput arguments[0]! encoded
    else if optStr arguments[0]! "nodeType" == some "Identifier" &&
        (← mType arguments[0]!) == "bytes memory" then bytes arguments[0]!
    else failAt init "raw static input requires selector encoding or existing memory bytes"
  let declarations ← mArr (← mField node "declarations")
  unless declarations.size == 2 && declarations.all (!·.isNull) do
    failAt node s!"{label} call requires a bool and memory bytes tuple"
  let success := declarations[0]!
  let data := declarations[1]!
  unless (← mType success) == "bool" && (← mType data) == "bytes" &&
      optStr data "storageLocation" == some "memory" do
    failAt node s!"{label} call requires a bool and memory bytes tuple"
  let sid ← mNat (← mField success "id")
  let sname ← mStr (← mField success "name")
  let result ← freshFor sname
  let did ← mNat (← mField data "id")
  let dname ← mStr (← mField data "name")
  modify fun e => { e with
    values := e.values.insert sid (.localVar result), scalarTy := e.scalarTy.insert sid .bool
    writableLocals := e.writableLocals.insert sid result
    yulNames := e.yulNames.insert sname (.localVar result), encodingMemory := true }
  let mut pre := target.pre ++ input.pre
  let mut gas := Expr.literal (2^256 - 1)
  if (← get).sourceGas then
    let observed ← fresh
    let site ← mStr (← mField init "src")
    pre := pre.push (.ecm (Compiler.ECM.SourceGasRead.module observed site) [])
    gas := .localVar observed
  let headerName ← fresh
  let sizeName ← fresh
  let header := Expr.localVar headerName
  let size := Expr.localVar sizeName
  let capacity := Expr.bitAnd (.add size (.literal 31)) (.bitNot (.literal 31))
  let call := if isStatic then
    Stmt.ecm (Compiler.ECM.SolidityRawStaticCall.module result)
      [gas, target.expr, input.pointer, input.size]
    else Stmt.ecm (Compiler.ECM.SolidityRawCall.module result false)
      [gas, target.expr, .literal 0, input.pointer, input.size]
  pre := pre ++ #[call,
    .letVar headerName (.literal 96), .letVar sizeName .returndataSize,
    .ite (.gt size (.literal 0)) [
      .assignVar headerName (.mload (.literal 64)),
      .mstore (.literal 64) (.add (.add header (.literal 32)) capacity),
      .mstore header size,
      .returndataCopy (.add header (.literal 32)) (.literal 0) size] []]
  let bound ← LegacyBytePointers.bind did dname
    { pre := #[], pointer := .add header (.literal 32), size }
  return pre ++ bound

end Compiler.CompilationModel.SolidityImport.LegacyCallTuples
