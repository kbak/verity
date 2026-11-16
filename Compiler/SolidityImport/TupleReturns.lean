import Compiler.SolidityImport.ExprHelpers

/-! Definite initialization for named storage results. A result slot is an address,
so scalar-style zero initialization must never make an unassigned reference readable. -/
namespace Compiler.CompilationModel.SolidityImport.TupleReturns
open Lean

/-- Whether solc describes a storage struct reference, including result declarations. -/
def isStorage (node : Json) : Bool :=
  let ty := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
  ty.startsWith "struct " && !ty.contains '[' &&
    (optStr node "storageLocation" == some "storage" ||
      ty.endsWith " storage ref" || ty.endsWith " storage pointer")

/-- Named storage results are the only reference assignment targets admitted here. -/
def namedStorageIds (fn : Json) : Array Nat := Id.run do
  let rets := ((field? fn "returnParameters").bind (field? · "parameters")).bind
    (·.getArr?.toOption) |>.getD #[]
  unless !rets.isEmpty && #[some "internal", some "private"].contains
      (optStr fn "visibility") do return #[]
  return rets.filterMap fun r =>
    if isStorage r && optStr r "name" != some "" then
      (field? r "id").bind (·.getNat?.toOption)
    else none

/-- Return declaration identity is preserved through tuple assignment targets. -/
def targetId? (node : Json) (ids : Array Nat) : Option Nat := do
  guard (optStr node "nodeType" == some "Identifier")
  let id ← (field? node "referencedDeclaration").bind (·.getNat?.toOption)
  guard (ids.contains id)
  return id

private partial def reads (node : Json) (ids : Array Nat) (assigned : Std.HashSet Nat) :
    M Unit := do
  if let some id := targetId? node ids then
    unless assigned.contains id do failAt node "storage tuple result is not definitely initialized"
  match node with
  | .arr xs => xs.forM (reads · ids assigned)
  | .obj fields => fields.toList.forM fun (_, child) => reads child ids assigned
  | _ => pure ()

private def allAssigned (node : Json) (ids : Array Nat) (assigned : Std.HashSet Nat) :
    M Unit := do
  unless ids.all assigned.contains do
    failAt node "storage tuple result is not definitely initialized on every return path"

private partial def flow (node : Json) (ids : Array Nat) (assigned : Std.HashSet Nat) :
    M (Option (Std.HashSet Nat)) := do
  match optStr node "nodeType" with
  | some "Block" | some "UncheckedBlock" =>
      let mut state := some assigned
      for stmt in (← mArr (← mField node "statements")) do
        if let some current := state then state ← flow stmt ids current
      return state
  | some "IfStatement" =>
      reads (← mField node "condition") ids assigned
      let yes ← flow (← mField node "trueBody") ids assigned
      let no ← match (field? node "falseBody").filter (!·.isNull) with
        | some body => flow body ids assigned
        | none => pure (some assigned)
      return match yes, no with
        | none, other | other, none => other
        | some a, some b => some (ids.foldl (fun acc id =>
            if a.contains id && b.contains id then acc.insert id else acc) {})
  | some "Return" =>
      let expr := field? node "expression" |>.getD Json.null
      if expr.isNull then allAssigned node ids assigned else reads expr ids assigned
      return none
  | some "RevertStatement" =>
      reads node ids assigned
      return none
  | some "ExpressionStatement" =>
      let expr ← mField node "expression"
      if optStr expr "nodeType" == some "Assignment" && optStr expr "operator" == some "=" then
        reads (← mField expr "rightHandSide") ids assigned
        let lhs ← mField expr "leftHandSide"
        let targets ← if optStr lhs "nodeType" == some "TupleExpression" then
            mArr (← mField lhs "components") else pure #[lhs]
        let mut next := assigned
        for target in targets do
          if let some id := targetId? target ids then next := next.insert id
          else reads target ids assigned
        return some next
      reads expr ids assigned
      let callee := field? expr "expression" |>.getD Json.null
      if optStr expr "nodeType" == some "FunctionCall" &&
          optStr callee "nodeType" == some "Identifier" && optStr callee "name" == some "revert" &&
          ((field? callee "referencedDeclaration").bind (·.getInt?.toOption)).any (· < 0) then
        return none
      return some assigned
  | _ =>
      -- Loops cannot establish definite assignment: their body may not run.
      reads node ids assigned
      return some assigned

/-- Check before emitting any default-initialized runtime address binding. -/
def validate (fn : Json) : M Unit := do
  let ids := namedStorageIds fn
  unless ids.isEmpty do
    if let some final ← flow (← mField fn "body") ids {} then
      allAssigned fn ids final

/-- Storage result initialization requires the body to execute on every successful path.
The common modifier lowering additionally rejects repeated/nested placeholders and returns. -/
def validateModifiers (modifiers : Array Json) : M Unit := do
  for invocation in modifiers do
    let id ← refInt (← mField invocation "modifierName")
    let some declaration := (← get).modifiers.find? id.toNat
      | failAt invocation "unresolved storage tuple modifier"
    let statements ← mArr (← mField (← mField declaration "body") "statements")
    unless id ≥ 0 && statements.any (optStr · "nodeType" == some "PlaceholderStatement") do
      failAt invocation "storage tuple modifiers require an unconditional body placeholder"

end Compiler.CompilationModel.SolidityImport.TupleReturns
