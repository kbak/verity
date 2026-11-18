import Compiler.SolidityImport.LegacyStructs

/-! A field-value projection of fixed-storage-array records copied to unaliased memory locals. -/
open Lean

namespace Compiler.CompilationModel.SolidityImport.RecordSnapshot

/-- IDs of exact assignments, destination records and stable words that must be nonzero. -/
structure Scope where
  assignments : Std.HashSet Nat := {}
  destinations : Std.HashSet Nat := {}
  nonzero : List String := []

private def ident? (j : Json) : Option Nat := do
  guard (optStr j "nodeType" == some "Identifier")
  (← field? j "referencedDeclaration").getNat?.toOption

private def astId? (j : Json) := (field? j "id").bind (·.getNat?.toOption)

private def children : Json → List Json
  | .arr a => a.toList
  | .obj o => o.toList.map Prod.snd
  | _ => []

private def fixed? (env : Env) (id : Nat) : Option FixedStorageStructArray :=
  env.fixedStructArrayVars.find? id <|> do
    let decl ← env.stateVars.find? id
    let name ← optStr decl "name"
    (← env.fieldsByName.find? name).fixedStructArray

/-- Only a direct scalar-record destination and an index into its declaration-matched,
captured fixed storage array can use the specialized copy. -/
private def destination? (env : Env) (j : Json) : Option Nat := do
  guard (optStr j "nodeType" == some "Assignment" && optStr j "operator" == some "=")
  let dest ← ident? (← field? j "leftHandSide")
  let flat ← env.flatStructs.find? dest
  let rhs ← field? j "rightHandSide"
  guard (optStr rhs "nodeType" == some "IndexAccess")
  let base ← field? rhs "baseExpression"
  let descriptor ← fixed? env (← ident? base)
  guard (LegacyStructs.fixedArray? base == some (flat.structId, descriptor.length) &&
    descriptor.structId == flat.structId && descriptor.wordCount > 0)
  return dest

private partial def collect (env : Env) (j : Json) (scope : Scope) : Scope := Id.run do
  let mut acc := scope
  let expr := (field? j "expression").getD .null
  if optStr j "nodeType" == some "ExpressionStatement" then
    if let (some dest, some id) := (destination? env expr, astId? expr) then
      acc := { acc with
        assignments := acc.assignments.insert id
        destinations := acc.destinations.insert dest }
  return (children j).foldl (fun s n => collect env n s) acc

/-- A destination may be rebound by an admitted copy and read by a declared scalar member.
Any other identifier use could export its pointer or preserve an alias to old memory. -/
private partial def checkUses (env : Env) (scope : Scope) (j : Json) : M Unit := do
  if (astId? j).any scope.assignments.contains then
    checkUses env scope (← mField j "rightHandSide")
    return
  if LegacyStructs.memoryMember j env &&
      ((field? j "expression").bind ident?).any scope.destinations.contains then return
  if (ident? j).any scope.destinations.contains || optStr j "nodeType" == some "InlineAssembly" then
    failAt j ("record snapshot requires independent local destinations " ++
      "and unobservable memory addresses")
  for child in children j do checkUses env scope child

private def allowedExpr : Expr → Bool
  | .literal _ | .localVar _ | .param _ | .storage _ | .storageArrayElement _ _
  | .calldatasize | .calldataload _ | .blockTimestamp | .blockNumber | .contractAddress
  | .caller | .msgValue | .add .. | .sub .. | .mul .. | .div .. | .mod .. | .sdiv ..
  | .smod .. | .signextend .. | .shl .. | .shr .. | .sar .. | .bitAnd .. | .bitOr ..
  | .bitXor .. | .bitNot .. | .logicalNot .. | .eq .. | .gt .. | .lt .. | .slt ..
  | .sgt .. | .le .. | .ge .. | .ite .. => true
  | _ => false

private def allowedStmt : Stmt → Bool
  | .letVar .. | .assignVar .. | .ite .. | .setStorage .. | .setStorageArrayElement ..
  | .revertEmpty | .panicCode .. => true
  | .ecm mod args => mod == Compiler.ECM.SolidityInvalid.module && args.isEmpty
  | _ => false

private partial def divisors (expr : Expr) : List Expr :=
  (match expr with | .div _ d | .mod _ d | .sdiv _ d | .smod _ d => [d] | _ => []) ++
    expr.children.flatMap divisors

private def stableDivisors (node : Json) (body : List Stmt) (env : Env) : M (List String) := do
  let written := Stmt.foldList (fun (set : Std.HashSet String) _ md =>
    (md.scopeEffects.bindNames ++ md.scopeEffects.assignNames).foldl (·.insert ·) set) {} body
  let ds := Stmt.foldList (fun acc _ md => md.subexpressions.flatMap divisors ++ acc) [] body
  let mut required : Std.HashSet String := {}
  for d in ds do
    match d with
    | .literal n => if n % 2^256 == 0 then failAt node "record snapshot has a zero divisor"
    | .param name | .localVar name =>
      unless env.bound.contains name && !written.contains name do
        failAt node "record snapshot requires stable scalar divisors"
      required := required.insert name
    | _ => failAt node "record snapshot requires literal or stable scalar divisors"
  return required.toList.mergeSort

private def addMemoryRecord (ids : Std.HashSet Nat) (decl : Json) : Std.HashSet Nat :=
  if optStr decl "storageLocation" == some "memory" then
    (astId? decl).elim ids ids.insert
  else ids

private partial def freshRecords (j : Json) (ids : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  if optStr j "nodeType" == some "VariableDeclarationStatement" &&
      (field? j "initialValue").any (fun v => optStr v "kind" == some "structConstructorCall") then
    if let some ds := (field? j "declarations").bind (·.getArr?.toOption) then
      return ds.foldl addMemoryRecord ids
  return (children j).foldl (fun acc child => freshRecords child acc) ids

/-- Compute and validate the field projection of the selected iteration. The whole defining
frame is scanned for alias escapes, and the executable step excludes raw allocation observers.
Every source storage read, write and array index check uses the ordinary lowering. -/
def check (node : Json) (body : List Stmt) (frame : Env) : M Scope := do
  let nonzero ← if frame.legacyDivisionHalt then pure [] else stableDivisors node body frame
  let scope := collect frame node { nonzero }
  if scope.assignments.isEmpty then return scope
  let some owner := frame.stack.head?.bind frame.funs.find? | failAt node "missing snapshot frame"
  let returns ← mArr (← mField (← mField owner "returnParameters") "parameters")
  let fresh := freshRecords owner (returns.foldl addMemoryRecord {})
  for dest in scope.destinations do
    unless fresh.contains dest do
      failAt node "snapshot destinations must be fresh memory records in this frame"
  let members := frame.flatStructs.toList.flatMap fun (_, flat) =>
    flat.members.toList.map fun (_, _, binding) => binding
  unless members.length == (Std.HashSet.ofList members).size do
    failAt node "snapshot destinations share a member binding"
  checkUses frame scope owner
  if Stmt.anyDeepList (fun s => !allowedStmt s ||
      s.directMetadata.subexpressions.any (·.anyDeep fun e => !allowedExpr e)) body then
    failAt node "record snapshot requires a memory-independent scalar and storage iteration"
  return scope

end Compiler.CompilationModel.SolidityImport.RecordSnapshot
