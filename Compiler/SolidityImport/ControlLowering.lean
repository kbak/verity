import Compiler.SolidityImport.ControlFlow
import Compiler.SolidityImport.ExprHelpers

/-! Solidity structured control lowering, parameterized by the existing expression
and leaf-statement lowering. The ordinary bounded-model backend does not call it. -/

namespace Compiler.CompilationModel.SolidityImport.ControlLowering
open Lean ControlFlow

/-- The observed program retains the existing scalar expression and statement languages. -/
abbrev Body := List (Program Stmt Expr)

/-- Restore lexical bindings, retaining fresh names, discoveries and loop-write invalidation. -/
private def restore (saved : Env) (writes : List Nat) : M Unit :=
  modify fun e =>
    { e with
      values := saved.values
      writableLocals := saved.writableLocals
      scalarTy := saved.scalarTy
      yulNames := saved.yulNames
      zeroInitLocals := saved.zeroInitLocals.filter (!writes.contains ·) }

/-- Lower a scalar control body. Declarations are checked before the leaf callback
so this initial API cannot capture aggregate or storage aliases without scope support. -/
partial def lower (expression : Json → M Val) (leaf : Json → M (Array Stmt))
    (node : Json) (depth : Nat := 0)
    (special : Json → Nat → M (Option Body) := fun _ _ => pure none) : M Body := do
  if let some body ← special node depth then return body
  match ← mKind node with
  | "Block" =>
      let saved ← get
      let mut chunks : Array Body := #[]
      for statement in (← mArr (← mField node "statements")) do
        chunks := chunks.push (← lower expression leaf statement depth special)
      restore saved (bodyAssignedIds node)
      return chunks.toList.flatten
  | "IfStatement" =>
      let condition ← expression (← mField node "condition")
      let saved ← get
      let yes ← lower expression leaf (← mField node "trueBody") depth special
      restore saved (bodyAssignedIds node)
      let noNode := (field? node "falseBody").getD Json.null
      let no ← if noNode.isNull then pure [] else lower expression leaf noNode depth special
      restore saved (bodyAssignedIds node)
      return [.branch condition.pre.toList condition.expr yes no]
  | "WhileStatement" | "ForStatement" =>
      let saved ← get
      let init := (field? node "initializationExpression").getD Json.null
      let initialBody ← if init.isNull then pure [] else lower expression leaf init depth special
      let conditionNode := (field? node "condition").getD Json.null
      let condition ← if conditionNode.isNull then pure ({ pre := #[], expr := .literal 1 } : Val)
        else expression conditionNode
      let loopScope ← get
      let body ← lower expression leaf (← mField node "body") (depth + 1) special
      restore loopScope (bodyAssignedIds node)
      let postNode := (field? node "loopExpression").getD Json.null
      let post ← if postNode.isNull then pure [] else lower expression leaf postNode depth special
      restore saved (bodyAssignedIds node)
      return initialBody ++ [.loop condition.pre.toList condition.expr body post]
  | "Break" | "Continue" =>
      unless depth > 0 do failAt node "observed loop control has no enclosing loop"
      return [if (← mKind node) == "Break" then .breakLoop else .continueLoop]
  | "VariableDeclarationStatement" =>
      for declaration in (← mArr (← mField node "declarations")) do
        unless !declaration.isNull && (paramType (← mType declaration)).isSome do
          failAt declaration "observed loop locals require scalar declarations"
      return (← leaf node).toList.map Program.atom
  | "ExpressionStatement" | "Return" =>
      return (← leaf node).toList.map Program.atom
  | other => failAt node s!"observed scalar control does not support {other}"

end Compiler.CompilationModel.SolidityImport.ControlLowering
