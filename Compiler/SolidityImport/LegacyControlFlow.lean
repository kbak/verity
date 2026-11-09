import Compiler.SolidityImport.ExprHelpers

/-! Conservative path evidence for legacy division and bounded loop admission.
Facts concern unsigned local declarations that are never assigned in the reached
function. This intentionally excludes mutable denominators, state reads, casts,
and interprocedural assumptions; no runtime zero-divisor behavior is invented. -/

open Lean
namespace Compiler.CompilationModel.SolidityImport

private def child (node : Json) (key : String) : Json :=
  field? node key |>.getD Json.null

private partial def unparen (node : Json) : Json :=
  if optStr node "nodeType" == some "TupleExpression" then
    match (field? node "components").bind (·.getArr?.toOption) with
    | some #[item] => unparen item
    | _ => node
  else node

private def naturalLiteral? (node : Json) : Option Nat := do
  let node := unparen node
  unless optStr node "nodeType" == some "Literal" do none
  let ty ← (field? node "typeDescriptions").bind (optStr · "typeString")
  unless ty.startsWith "int_const " do none
  (ty.drop "int_const ".length).toString.toNat?

private def identifier? (node : Json) : Option Nat := do
  let node := unparen node
  unless optStr node "nodeType" == some "Identifier" do none
  let id ← (field? node "referencedDeclaration").bind (·.getInt?.toOption)
  if id < 0 then none else some id.toNat

private partial def unsignedDeclarations (node : Json)
    (ids : Std.HashSet Nat := {}) : Std.HashSet Nat := Id.run do
  match node with
  | .arr xs => return xs.foldl (fun acc x => unsignedDeclarations x acc) ids
  | .obj fields =>
    let mut ids := ids
    if optStr node "nodeType" == some "VariableDeclaration" &&
        (child node "stateVariable").getBool?.toOption != some true then
      let ty := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
      if ty.startsWith "uint" && (bitsOf ty).isSome then
        if let some id := (field? node "id").bind (·.getNat?.toOption) then
          ids := ids.insert id
    for (_, value) in fields do ids := unsignedDeclarations value ids
    return ids
  | _ => return ids

private def meet (a b : Std.HashSet Nat) : Std.HashSet Nat :=
  a.toList.foldl (fun acc id => if b.contains id then acc.insert id else acc) {}

private partial def branchFacts (node : Json) (truth : Bool)
    (eligible facts : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  let node := unparen node
  if optStr node "nodeType" == some "UnaryOperation" &&
      optStr node "operator" == some "!" then
    return branchFacts (child node "subExpression") (!truth) eligible facts
  if optStr node "nodeType" != some "BinaryOperation" then return facts
  let op := optStr node "operator" |>.getD ""
  let lhs := child node "leftExpression"
  let rhs := child node "rightExpression"
  if (op == "&&" && truth) || (op == "||" && !truth) then
    return branchFacts rhs truth eligible (branchFacts lhs truth eligible facts)
  let candidate :=
    if naturalLiteral? rhs == some 0 &&
        ((truth && (op == "!=" || op == ">")) || (!truth && (op == "==" || op == "<="))) then
      identifier? lhs
    else if naturalLiteral? lhs == some 0 &&
        ((truth && (op == "!=" || op == "<")) || (!truth && (op == "==" || op == ">="))) then
      identifier? rhs
    else none
  if let some id := candidate then
    if eligible.contains id then return facts.insert id
  return facts

private def builtin? (node : Json) (name : String) : Bool :=
  optStr node "nodeType" == some "FunctionCall" &&
    (let callee := child node "expression"
     optStr callee "nodeType" == some "Identifier" && optStr callee "name" == some name &&
       ((field? callee "referencedDeclaration").bind (·.getInt?.toOption)).any (· < 0))

private partial def validateExpression (node : Json)
    (eligible facts : Std.HashSet Nat) : M Unit := do
  let kind := optStr node "nodeType"
  let op := optStr node "operator" |>.getD ""
  if kind == some "BinaryOperation" && (op == "&&" || op == "||") then
    let lhs := child node "leftExpression"
    validateExpression lhs eligible facts
    validateExpression (child node "rightExpression") eligible
      (branchFacts lhs (op == "&&") eligible facts)
    return
  if (kind == some "BinaryOperation" && (op == "/" || op == "%")) ||
      (kind == some "Assignment" && (op == "/=" || op == "%=")) then
    let rhs := child node (if kind == some "Assignment" then "rightHandSide" else "rightExpression")
    let constant := (naturalLiteral? rhs).any (fun n => 0 < n && n < 2 ^ 256)
    let guarded := (identifier? rhs).any facts.contains
    unless constant || guarded do
      failAt node ("Solidity 0.7.6 division/modulo needs a nonzero literal or an " ++
        "immutable local guarded on every reaching path; legacy exceptional halt is not modeled")
  match node with
  | .arr xs => xs.forM (fun x => validateExpression x eligible facts)
  | .obj fields =>
    for (_, value) in fields do validateExpression value eligible facts
  | _ => pure ()

/-- Loop admission excludes alternate modern lowering paths with heuristic bounds. -/
def validateLegacyLoop (node : Json) : M Unit := do
  let cond := unparen (child node "condition")
  unless optStr cond "nodeType" == some "BinaryOperation" do
    failAt node "Solidity 0.7.6 loops require a supported monotone bound"
  let op := optStr cond "operator" |>.getD ""
  let lhs := child cond "leftExpression"
  let rhs := child cond "rightExpression"
  if optStr node "nodeType" == some "WhileStatement" then
    unless ((op == "!=" || op == ">") && naturalLiteral? rhs == some 0 &&
        (identifier? lhs).isSome) ||
        ((op == "!=" || op == "<") && naturalLiteral? lhs == some 0 &&
        (identifier? rhs).isSome) do
      failAt node "Solidity 0.7.6 while loops require an unsigned local compared with zero"
    return
  unless op == "<" do
    failAt node "Solidity 0.7.6 for loops require counter < invariant bound"
  let init := child node "initializationExpression"
  let start := if optStr init "nodeType" == some "VariableDeclarationStatement" then
      child init "initialValue" else child (child init "expression") "rightHandSide"
  unless start.isNull || naturalLiteral? start == some 0 do
    failAt init "Solidity 0.7.6 for loops must start at zero"
  let writes := bodyAssignedIds (child node "body")
  let bound := unparen rhs
  let boundId := if optStr bound "nodeType" == some "MemberAccess" &&
      optStr bound "memberName" == some "length" then identifier? (child bound "expression")
    else identifier? bound
  if let some id := boundId then
    if writes.contains id || identifier? lhs == some id then
      failAt bound "Solidity 0.7.6 for loop bound must remain invariant"

private partial def validateFlow (node : Json) (eligible facts : Std.HashSet Nat) :
    M (Option (Std.HashSet Nat)) := do
  match optStr node "nodeType" with
  | some "Block" =>
    let mut out := some facts
    for stmt in (← mArr (← mField node "statements")) do
      if let some current := out then out ← validateFlow stmt eligible current
    return out
  | some "IfStatement" =>
    let cond := child node "condition"
    validateExpression cond eligible facts
    let yes ← validateFlow (child node "trueBody") eligible (branchFacts cond true eligible facts)
    let no ← validateFlow (child node "falseBody") eligible (branchFacts cond false eligible facts)
    return match yes, no with
      | some a, some b => some (meet a b)
      | some a, none | none, some a => some a
      | none, none => none
  | some "Return" =>
    validateExpression (child node "expression") eligible facts
    return none
  | some "ForStatement" | some "WhileStatement" =>
    validateLegacyLoop node
    let init ← validateFlow (child node "initializationExpression") eligible facts
    let current := init.getD facts
    let cond := child node "condition"
    validateExpression cond eligible current
    let body ← validateFlow (child node "body") eligible (branchFacts cond true eligible current)
    discard (validateFlow (child node "loopExpression") eligible (body.getD current))
    return some current
  | some "ExpressionStatement" =>
    let expr := child node "expression"
    validateExpression expr eligible facts
    if builtin? expr "revert" then return none
    if builtin? expr "require" then
      if let some args := (field? expr "arguments").bind (·.getArr?.toOption) then
        if let some cond := args[0]? then
          return some (branchFacts cond true eligible facts)
    return some facts
  | _ =>
    validateExpression node eligible facts
    return some facts

/-- Each reached declaration proves its own division guards; caller assumptions
are never imported. Restricting facts to never-assigned local IDs makes them
stable across joins, loop iterations, inline assembly, and internal calls. -/
def validateLegacyControlFlow (fn : Json) : M Unit := do
  let body := child fn "body"
  let writes := (bodyAssignedIds body).foldl (fun (s : Std.HashSet Nat) id => s.insert id) {}
  let eligible := (unsignedDeclarations fn).toList.foldl
    (fun (s : Std.HashSet Nat) id => if writes.contains id then s else s.insert id) {}
  discard (validateFlow body eligible {})

/-- Normalize the legacy existing-counter spelling for the exact counted-loop
lowerer. The caller must emit initialization and restore the observable final
counter; the synthetic declaration alone would lose that final assignment. -/
def legacyAssignedFor? (node : Json) : M (Option (Json × Nat)) := do
  let init := child node "initializationExpression"
  unless optStr init "nodeType" == some "ExpressionStatement" do return none
  let expr := child init "expression"
  let lhs := child expr "leftHandSide"
  let some id := identifier? lhs | failAt init "a for loop must initialize a scalar counter"
  unless optStr expr "nodeType" == some "Assignment" && optStr expr "operator" == some "=" &&
      naturalLiteral? (child expr "rightHandSide") == some 0 && (← mType lhs) == "uint256" do
    failAt init "a legacy existing for counter must be uint256 and initialized to zero"
  unless ((← get).writableLocals.find? id).isSome do
    failAt lhs "a for loop counter must be a writable scalar local"
  let decl := Json.mkObj [("nodeType", .str "VariableDeclaration"), ("id", toJson id),
    ("name", child lhs "name"), ("typeDescriptions", child lhs "typeDescriptions"),
    ("src", child lhs "src")]
  let replacement := Json.mkObj [("nodeType", .str "VariableDeclarationStatement"),
    ("declarations", .arr #[decl]), ("initialValue", child expr "rightHandSide"),
    ("src", child init "src")]
  let .obj fields := node | return none
  return some (Json.mkObj (fields.toList.map fun (key, value) =>
    (key, if key == "initializationExpression" then replacement else value)), id)

end Compiler.CompilationModel.SolidityImport
