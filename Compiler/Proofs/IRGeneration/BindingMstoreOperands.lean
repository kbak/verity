import Compiler.Proofs.IRGeneration.BoundedMstoreExecution

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel SourceSemantics

/-- Bounded scalar operands that depend only on present parameter/local bindings.
Constant additions are exact natural-number additions, with no modular wrap. -/
inductive BindingMstoreOperand (bindings : List (String × Nat)) : Expr → Nat → Prop where
  | literal (number : Nat) (bounded : number < Compiler.Constants.evmModulus) :
      BindingMstoreOperand bindings (.literal number) number
  | param (name : String) (number : Nat)
      (found : lookupBinding? bindings name = some number)
      (bounded : number < Compiler.Constants.evmModulus) :
      BindingMstoreOperand bindings (.param name) number
  | localVar (name : String) (number : Nat)
      (found : lookupBinding? bindings name = some number)
      (bounded : number < Compiler.Constants.evmModulus) :
      BindingMstoreOperand bindings (.localVar name) number
  | addLiteral {expr : Expr} {number : Nat}
      (base : BindingMstoreOperand bindings expr number) (delta : Nat)
      (bounded : number + delta < Compiler.Constants.evmModulus) :
      BindingMstoreOperand bindings (.add expr (.literal delta)) (number + delta)

/-- Agreement only on the bindings referenced by a supported scalar operand. -/
def MstoreOperandBindingsAgree (left right : List (String × Nat)) : Expr → Prop
  | .literal _ => True
  | .param name | .localVar name => lookupBinding? left name = lookupBinding? right name
  | .add base (.literal _) => MstoreOperandBindingsAgree left right base
  | _ => False

/-- A bounded constant addition evaluates without truncating either operand or the sum. -/
theorem eval_canonical_add_literal_of_eval (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (expr : Expr) (number delta : Nat)
    (resolved : evalExprCanonical spec fields state expr = some number)
    (bounded : number + delta < Compiler.Constants.evmModulus) :
    evalExprCanonical spec fields state (.add expr (.literal delta)) =
      some (number + delta) := by
  have hDelta : evalExprCanonical spec fields state (.literal delta) = some delta :=
    eval_canonical_literal_of_lt spec fields state delta (by omega)
  unfold evalExprCanonical at resolved hDelta ⊢
  rw [evalExprWithHelpers.eq_def]
  simp only [resolved, hDelta]
  change some ((number % Compiler.Constants.evmModulus +
    delta % Compiler.Constants.evmModulus) % Compiler.Constants.evmModulus) = _
  rw [Nat.mod_eq_of_lt (show number < Compiler.Constants.evmModulus by omega),
    Nat.mod_eq_of_lt (show delta < Compiler.Constants.evmModulus by omega),
    Nat.mod_eq_of_lt bounded]

/-- Operand evidence determines canonical evaluation independently of memory and world state. -/
theorem eval_canonical_binding_mstore_operand (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (expr : Expr) (number : Nat)
    (operand : BindingMstoreOperand state.bindings expr number) :
    evalExprCanonical spec fields state expr = some number := by
  induction operand with
  | literal number bounded => exact eval_canonical_literal_of_lt spec fields state number bounded
  | param name number found _ | localVar name number found _ =>
      simp only [evalExprCanonical_param, evalExprCanonical_localVar]
      change some ((lookupBinding? state.bindings name).getD 0) = some number
      rw [found]
      rfl
  | addLiteral base delta bounded ih =>
      exact eval_canonical_add_literal_of_eval spec fields state _ _ delta ih bounded

/-- Equal referenced bindings transport operand evidence without equating unrelated bindings. -/
theorem binding_mstore_operand_of_bindings_agree
    {left right : List (String × Nat)} {expr : Expr} {number : Nat}
    (operand : BindingMstoreOperand left expr number)
    (same : MstoreOperandBindingsAgree left right expr) :
    BindingMstoreOperand right expr number := by
  induction operand with
  | literal number bounded => exact .literal number bounded
  | param name number found bounded => exact .param name number (same ▸ found) bounded
  | localVar name number found bounded => exact .localVar name number (same ▸ found) bounded
  | addLiteral base delta bounded ih => exact .addLiteral (ih same) delta bounded

end Compiler.Proofs.IRGeneration
