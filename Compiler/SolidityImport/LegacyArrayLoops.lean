import Compiler.SolidityImport.ExprHelpers

/-! Exact bounded lowering of address traversal that writes one array cell per
iteration. The mandatory write fails with INVALID at capacity, so the extra
iteration preserves failure on cycles and lists longer than the allocation. -/
open Lean
namespace Compiler.CompilationModel.SolidityImport.LegacyArrayLoops

private def child (node : Json) (key : String) : Json := field? node key |>.getD Json.null

private def identifier? (node : Json) : Option Nat := do
  unless optStr node "nodeType" == some "Identifier" do none
  (field? node "referencedDeclaration").bind (·.getNat?.toOption)

/-- Recognize only address inequality; unsigned bit loops retain their own lowerer. -/
def candidate (node : Json) : Bool :=
  let cond := child node "condition"
  optStr cond "nodeType" == some "BinaryOperation" && optStr cond "operator" == some "!=" &&
    ((field? (child cond "leftExpression") "typeDescriptions").bind (optStr · "typeString")) ==
      some "address"

/-- The checked syntax is write-at-index, update cursor, increment index. No
body declaration or arbitrary loop bound is synthesized. The source can stop at
any sentinel; both a missing sentinel and a cycle hit the original bounds check. -/
def lower (node : Json) (lowerExpr : Json → M Val)
    (lowerBody : Json → M (Array Stmt)) : M (Array Stmt) := do
  let cond := child node "condition"
  let body := child node "body"
  let fail : M (Array Stmt) := failAt node
    "Solidity 0.7.6 address traversal requires write, cursor update, and unit index step"
  unless optStr body "nodeType" == some "Block" do return ← fail
  let stmts ← mArr (← mField body "statements")
  unless stmts.size == 3 && stmts.all (fun s =>
      optStr s "nodeType" == some "ExpressionStatement") do return ← fail
  let write := child stmts[0]! "expression"
  let step := child stmts[1]! "expression"
  let increment := child stmts[2]! "expression"
  let target := child write "leftHandSide"
  let some arrayId := identifier? (child target "baseExpression") | return ← fail
  let some indexId := identifier? (child target "indexExpression") | return ← fail
  let some cursorId := identifier? (child cond "leftExpression") | return ← fail
  unless optStr write "nodeType" == some "Assignment" && optStr write "operator" == some "=" &&
      optStr target "nodeType" == some "IndexAccess" &&
      identifier? (child write "rightHandSide") == some cursorId &&
      optStr step "nodeType" == some "Assignment" && optStr step "operator" == some "=" &&
      identifier? (child step "leftHandSide") == some cursorId &&
      optStr increment "nodeType" == some "UnaryOperation" &&
      optStr increment "operator" == some "++" &&
      identifier? (child increment "subExpression") == some indexId do return ← fail
  -- Only the final increment may change the index. A nested update in the
  -- cursor expression would invalidate the capacity-based termination bound.
  if (bodyAssignedIds (child step "rightHandSide")).contains indexId then return ← fail
  let env ← get
  let some array := env.scalarArrays.find? arrayId | return ← fail
  unless array.inMemory && array.elementType == "address" &&
      env.zeroInitLocals.contains indexId &&
      (← mType (child increment "subExpression")) == "uint256" &&
      (env.writableLocals.find? cursorId).isSome do return ← fail
  -- The condition's RHS may not depend on either variable modified by the body.
  let rhs := child cond "rightExpression"
  let bound ← lowerExpr rhs
  unless bound.pre.isEmpty && (bound.expr matches .literal _) do
    failAt rhs "Solidity 0.7.6 address traversal requires a constant sentinel"
  let condition ← lowerExpr cond
  unless condition.pre.isEmpty do return ← fail
  let loop ← fresh
  let lowered ← lowerBody body
  return #[.forEach loop (.add (.localVar array.lengthBinding) (.literal 1))
    [.ite condition.expr lowered.toList []]]

end Compiler.CompilationModel.SolidityImport.LegacyArrayLoops
