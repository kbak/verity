import Compiler.SolidityImport.ExprHelpers

/-! Straight-line physical memory lowering. Unknown upper bits of Solidity scalars
are tracked per byte until overwritten. Every observable read must be independent
of those bits, and every address is subsequently checked in the enclosing root. -/
namespace Compiler.CompilationModel.SolidityImport.BoundedMemory
open Lean

private def wordMask : Nat := 2^256 - 1

private structure Value where
  term : Val
  dirty : Nat := 0
  pointer : Option (String × Int) := none

private structure Scratch where
  locals : Std.HashMap String (String × Value) := {}
  bytes : Std.HashMap Int Nat := {}
  externalVersions : Std.HashMap Nat Nat := {}
  base : Option String := none

private abbrev B := StateT Scratch M

private def modifyEnv (f : Env → Env) : B Unit := liftM (modify f : M Unit)

private def reject (node : Json) (message : String) : B α :=
  liftM (failAt node message)

private def clean (node : Json) (value : Value) : B Unit := do
  unless value.dirty == 0 do reject node "bounded memory observes dirty scalar bits"

private def scalarMask (ty : ParamType) : Nat :=
  let upper (bits : Nat) := wordMask - (2^bits - 1)
  match ty with
  | .uint8 => upper 8
  | .uint16 => upper 16
  | .uintN n | .intN n => upper (min n 256)
  | .address => upper 160
  | .bool => upper 1
  | .bytesN n => 2^(256 - min (8*n) 256) - 1
  | _ => 0

private def reference (node : Json) (refs : Array Json) : M Nat := do
  let src ← mStr (← mField node "src")
  let some ref := refs.find? (fun r => optStr r "src" == some src)
    | failAt node "unresolved bounded-memory scalar reference"
  unless field? ref "suffix" == none &&
      (← mBool (← mField ref "isOffset")) == false &&
      (← mBool (← mField ref "isSlot")) == false &&
      (← mNat (← mField ref "valueSize")) == 1 do
    failAt node "bounded memory requires scalar references without suffixes"
  mNat (← mField ref "declaration")

private def leaf (node : Json) (refs : Array Json) (lower : Json → M Val) : B Value := do
  if optStr node "nodeType" == some "YulIdentifier" then
    let name ← liftM (mStr (← mField node "name"))
    if let some (_, value) := (← get).locals[name]? then return value
    let id ← liftM (reference node refs)
    let env ← liftM (get : M Env)
    unless !env.enumBounds.contains id do reject node "bounded memory cannot read enum scalars"
    let some ty := env.scalarTy.find? id
      | reject node "bounded memory requires a known scalar type"
    let value ← liftM (lower node)
    unless value.pre.isEmpty do reject node "effectful bounded-memory scalar reference"
    let version := (← get).externalVersions[id]?.getD 0
    return {
      term := value
      dirty := scalarMask ty
      pointer := some (s!"scalar:{id}:{version}", 0) }
  let value ← liftM (lower node)
  match value.expr with
  | .literal n => return { term := value, pointer := some ("absolute", Int.ofNat n) }
  | _ => reject node "bounded memory requires numeric literals or scalar references"

private def address (node : Json) (value : Value) : B (String × Int) := do
  clean node value
  let some pointer := value.pointer | reject node "unsupported bounded-memory address expression"
  let scratch ← get
  unless scratch.bytes.isEmpty || scratch.base == some pointer.1 do
    reject node "bounded memory cannot establish disjointness from dirty bytes"
  return pointer

private def readMask (node : Json) (value : Value) (size : Nat) : B Nat := do
  let (_, offset) ← address node value
  let bytes := (← get).bytes
  return (List.range size).foldl (fun mask i =>
    mask * 256 + bytes[offset + Int.ofNat i]?.getD 0) 0

private def writeMask (node : Json) (addr value : Value) : B Unit := do
  let (base, offset) ← address node addr
  modify fun s => { s with base := some base }
  for i in [:32] do
    let at_ := offset + Int.ofNat i
    let mask := (value.dirty / 2^(8*(31-i))) % 256
    modify fun s => { s with bytes :=
      if mask == 0 then s.bytes.erase at_ else s.bytes.insert at_ mask }

private def register (node : Json) (value : Value) (size : Nat)
    (metadata : Bool := false) : B Val := do
  clean node value
  let binding ← liftM fresh
  modifyEnv fun e => { e with
    memoryAccesses := e.memoryAccesses.push
      { binding, size, metadata, node, file := e.currentFile, stack := e.stack } }
  return { pre := value.term.pre.push (.letVar binding value.term.expr), expr := .localVar binding }

private def shifted (a b : Value) : Option (String × Int) :=
  match a.pointer, b.term.expr with
  | some (base, offset), .literal n => some (base, offset + Int.ofNat n)
  | _, _ => none

private def binary (node : Json) (name : String) (a b : Value) : B Value := do
  let pre := a.term.pre ++ b.term.pre
  let x := a.term.expr
  let y := b.term.expr
  let joined := Nat.lor a.dirty b.dirty
  let literalMask (e : Expr) := match e with | .literal n => n | _ => wordMask
  match name with
  | "and" => return {
      term := { pre, expr := .bitAnd x y }
      dirty := Nat.lor (Nat.land a.dirty (literalMask y)) (Nat.land b.dirty (literalMask x)) }
  | "or" => return { term := { pre, expr := .bitOr x y }, dirty := joined }
  | "xor" => return { term := { pre, expr := .bitXor x y }, dirty := joined }
  | _ =>
    clean node a
    clean node b
    let expr ← match name with
      | "add" => pure (Expr.add x y)
      | "sub" => pure (.sub x y)
      | "mul" => pure (.mul x y)
      | "shl" => pure (.shl x y)
      | "shr" => pure (.shr x y)
      | "eq" => pure (.eq x y)
      | "lt" => pure (.lt x y)
      | "gt" => pure (.gt x y)
      | _ => reject node "unsupported bounded-memory word operation"
    let pointer := if name == "add" then shifted a b <|> shifted b a else none
    return { term := { pre, expr }, pointer }

private partial def expression (node : Json) (refs : Array Json)
    (lower : Json → M Val) : B Value := do
  if optStr node "nodeType" != some "YulFunctionCall" then return ← leaf node refs lower
  let name ← liftM (mStr (← mField (← mField node "functionName") "name"))
  let args ← liftM (mArr (← mField node "arguments"))
  let xs ← args.mapM (expression · refs lower)
  match name, xs with
  | "mload", #[a] =>
      let mask ← readMask node a 32
      let at_ ← register node a 32 true
      let metadata := match a.term.expr with | .literal 64 => true | _ => false
      let identity ← liftM fresh
      let pointer := if metadata then some (identity, 0) else none
      return {
        term := { pre := at_.pre, expr := .mload (if metadata then .literal 64 else at_.expr) }
        dirty := mask
        pointer }
  | "keccak256", #[a, b] =>
      clean node b
      let .literal size := b.term.expr
        | reject node "bounded memory requires a constant hash length"
      unless size ≤ 4096 do reject node "bounded memory hash length exceeds 4096 bytes"
      unless (← readMask node a size) == 0 do
        reject node "bounded memory hash observes dirty scalar bytes"
      let at_ ← register node a size
      return { term := { pre := at_.pre ++ b.term.pre, expr := .keccak256 at_.expr b.term.expr } }
  | "not", #[a] => return { term := { a.term with expr := .bitNot a.term.expr }, dirty := a.dirty }
  | _, #[a, b] => binary node name a b
  | _, _ => reject node "unsupported bounded-memory expression or arity"

/-- Record narrow references in older assembly paths. A root using the new
physical-memory fragment cannot rely on those paths having preserved dirty bits.
Roots outside this fragment retain their existing admission behavior. -/
def recordUncheckedReferences (assembly : Json) : M Unit := do
  let refs ← mArr (← mField assembly "externalReferences")
  for ref in refs do
    let id ← mNat (← mField ref "declaration")
    let env ← get
    if (env.scalarTy.find? id).any (fun ty => scalarMask ty != 0) then
      let src ← mField ref "src"
      let node := Json.mkObj [("nodeType", .str "YulIdentifier"), ("src", src)]
      modify fun e => { e with
        uncheckedAssemblyReferences := e.uncheckedAssemblyReferences.push
          { node, file := e.currentFile, stack := e.stack } }

private def scratchWord (node : Json) : Bool :=
  let first := (field? node "arguments").bind (·.getArr?.toOption) |>.bind (·[0]?)
  let value := first.bind (optStr · "value") |>.bind fun raw =>
    Compiler.Hex.parseHexNat? raw <|> raw.toNat?
  value == some 0 || value == some 32

/-- Existing literal scratch-word failures retain their original validators.
The new fragment addresses allocator metadata or nonscratch memory. -/
partial def applies (node : Json) : Bool :=
  match node with
  | .arr xs => xs.any applies
  | .obj fields =>
      ((optStr node "nodeType" == some "YulFunctionCall") && !scratchWord node &&
        ((field? node "functionName").bind (optStr · "name")).any
          (#["mload", "mstore", "keccak256"].contains ·)) ||
      fields.toList.any (fun (_, child) => applies child)
  | _ => false

/-- Reference descriptors and enum validation remain owned by existing paths;
this fragment can interpret only resolved scalar declaration references. -/
def scalarReferences (refs : Array Json) : M Bool := do
  let env ← get
  return refs.all fun ref =>
    ((field? ref "declaration").bind (·.getNat?.toOption)).any fun id =>
      env.scalarTy.contains id && !env.enumBounds.contains id

/-- Admit only straight-line assembly; unsupported effects stay located failures. -/
def lower (assembly : Json) (stmts refs : Array Json) (leafLower : Json → M Val)
    (assign : Json → Json → Val → M Stmt) : M (Array Stmt) := do
  let action : B (Array Stmt) := do
    let mut out := #[]
    for stmt in stmts do
      match ← liftM (mKind stmt) with
      | "YulVariableDeclaration" | "YulAssignment" =>
        let declaration := optStr stmt "nodeType" == some "YulVariableDeclaration"
        let targets ← liftM (mArr (← mField stmt
          (if declaration then "variables" else "variableNames")))
        unless targets.size == 1 do reject stmt "bounded memory requires one assignment target"
        let target := targets[0]!
        let name ← liftM (mStr (← mField target "name"))
        let value ← match field? stmt "value" with
          | some .null | none =>
              if declaration then
                pure {
                  term := { pre := #[], expr := .literal 0 }
                  pointer := some ("absolute", 0) }
              else reject stmt "bounded-memory assignment requires a value"
          | some valueNode => expression valueNode refs leafLower
        out := out ++ value.term.pre
        if declaration || (← get).locals.contains name then
          let binding ← if declaration then liftM (freshFor name)
            else do
              let some (binding, _) := (← get).locals[name]?
                | reject target "unbound bounded-memory local"
              pure binding
          if declaration then
            unless optStr target "type" == some "" && !(← get).locals.contains name do
              reject target "duplicate or typed bounded-memory local"
          out := out.push (if declaration then .letVar binding value.term.expr
            else .assignVar binding value.term.expr)
          -- A snapshot gets a stable symbolic identity even for a non-affine clean value.
          let identity ← liftM fresh
          let pointer := value.pointer.orElse fun _ => some (identity, 0)
          modify fun s => { s with
            locals := s.locals.insert name
              (binding, { value with term := { pre := #[], expr := .localVar binding }, pointer }) }
          modifyEnv fun e => { e with yulNames := e.yulNames.insert name (.localVar binding) }
        else
          clean target value
          let id ← liftM (reference target refs)
          let scratch ← get
          let version := scratch.externalVersions[id]?.getD 0
          if !scratch.bytes.isEmpty && scratch.base == some s!"scalar:{id}:{version}" then
            reject target "bounded memory cannot reassign a pointer to dirty bytes"
          let env ← liftM (get : M Env)
          let some ty := env.scalarTy.find? id
            | reject target "bounded memory requires a known assignment type"
          unless isFullWordYulScalar ty || isProvablyBoundedYulExpr ty value.term.expr do
            reject target "bounded memory cannot assign an unbounded word to a narrow scalar"
          out := out.push (← liftM (assign stmt target { pre := #[], expr := value.term.expr }))
          modify fun s => { s with
            externalVersions := s.externalVersions.insert id (s.externalVersions[id]?.getD 0 + 1) }
      | "YulExpressionStatement" =>
        let call ← liftM (mField stmt "expression")
        let name ← liftM (mStr (← mField (← mField call "functionName") "name"))
        let args ← liftM (mArr (← mField call "arguments"))
        unless name == "mstore" && args.size == 2 do
          reject stmt "bounded memory supports only mstore statements"
        let addr ← expression args[0]! refs leafLower
        let value ← expression args[1]! refs leafLower
        writeMask stmt addr value
        let at_ ← register call addr 32 true
        out := out ++ at_.pre ++ value.term.pre
        out := out.push (.mstore at_.expr value.term.expr)
      | _ => reject stmt "bounded memory requires straight-line assembly"
    unless (← get).bytes.isEmpty do
      reject assembly "bounded memory leaves dirty scalar bytes visible after assembly"
    return out
  action.run' {}

end Compiler.CompilationModel.SolidityImport.BoundedMemory
