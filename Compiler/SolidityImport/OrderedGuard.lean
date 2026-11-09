import Compiler.SolidityImport.ReadOnlyFrames

namespace Compiler.CompilationModel.SolidityImport.OrderedGuard
open Denote
open AuthorizationFrames

/-- Local names used by the lowered short-circuit ordering/membership guard. -/
abbrev Names := Fin 8 → String

/-- The complete common guard, including the update of the preceding signer. -/
def body (n : Names) (field member : String) (sentinel : Nat) (failure : List Stmt) : List Stmt :=
  [.letVar (n 2) (.le (.localVar (n 0)) (.localVar (n 1))),
   .letVar (n 3) (.localVar (n 2)),
   .ite (.localVar (n 2)) []
     [.letVar (n 4) (.structMember field (.localVar (n 0)) member),
      .assignVar (n 3) (.eq (.localVar (n 4)) (.literal 0))],
   .letVar (n 5) (.localVar (n 3)),
   .letVar (n 6) (.localVar (n 5)),
   .ite (.localVar (n 5)) [] [.assignVar (n 6) (.eq (.localVar (n 0)) (.literal sentinel))],
   .letVar (n 7) (.localVar (n 6)),
   .ite (.localVar (n 7)) failure [],
   .assignVar (n 1) (.localVar (n 0))]

/-- Lookup through generated temporary assignments needs only name freshness. -/
theorem lookup_named (n : Names) (fresh : Function.Injective n) (env : Denote.Env)
    (i j : Fin 8) (value : Nat) :
    lookupValue (bindValue env (n i) value) (n j) =
      if i = j then value else lookupValue env (n j) := by
  by_cases same : i = j
  · subst j; simp
  · rw [if_neg same, lookup_bind_other _ _ _ _ (fun h => same (fresh h))]

/-- The two flag stores preceding a member read leave its argument unchanged. -/
theorem member_two_temps (n : Names) (fresh : Function.Injective n)
    (o : DenoteOracle) (fs : List Field) (state : DenoteState)
    (field member : String) (value : Nat) :
    evalExpr o fs { state with
      bindings := bindValue (bindValue state.bindings (n 2) value) (n 3) value }
      (.structMember field (.localVar (n 0)) member) =
    evalExpr o fs state (.structMember field (.localVar (n 0)) member) := by
  simp [evalExpr, lookup_named n fresh]

/-- Zero remains zero under uint256 normalization. -/
@[simp] theorem normalized_zero : wordNormalize 0 = 0 := rfl

/-- Scalar step equations keep the generic expression evaluator opaque to clients. -/
theorem eval_local (o : DenoteOracle) (fs : List Field) (state : DenoteState) (name : String) :
    evalExpr o fs state (.localVar name) = some (lookupValue state.bindings name) := rfl

/-- Literals use the interpreter's uint256 normalization. -/
theorem eval_literal (o : DenoteOracle) (fs : List Field) (state : DenoteState) (value : Nat) :
    evalExpr o fs state (.literal value) = some (wordNormalize value) := rfl

/-- Ordering is applied to evaluated words. -/
theorem eval_le (o : DenoteOracle) (fs : List Field) (state : DenoteState) (a b : Expr) :
    evalExpr o fs state (.le a b) = (do
      let x ← evalExpr o fs state a
      let y ← evalExpr o fs state b
      pure (boolWord (decide (x ≤ y)))) := rfl

/-- Equality is applied to evaluated words. -/
theorem eval_eq (o : DenoteOracle) (fs : List Field) (state : DenoteState) (a b : Expr) :
    evalExpr o fs state (.eq a b) = (do
      let x ← evalExpr o fs state a
      let y ← evalExpr o fs state b
      pure (boolWord (decide (x = y)))) := rfl

/-- First short-circuit stage: compare with the preceding signer and read membership. -/
def first (n : Names) (field member : String) : List Stmt :=
  [.letVar (n 2) (.le (.localVar (n 0)) (.localVar (n 1))),
   .letVar (n 3) (.localVar (n 2)),
   .ite (.localVar (n 2)) []
     [.letVar (n 4) (.structMember field (.localVar (n 0)) member),
      .assignVar (n 3) (.eq (.localVar (n 4)) (.literal 0))]]

/-- Second short-circuit stage: add the distinguished-address exclusion. -/
def second (n : Names) (sentinel : Nat) : List Stmt :=
  [.letVar (n 5) (.localVar (n 3)), .letVar (n 6) (.localVar (n 5)),
   .ite (.localVar (n 5)) [] [.assignVar (n 6) (.eq (.localVar (n 0)) (.literal sentinel))]]

/-- Final stage: reject the computed flag, then record the current signer. -/
def last (n : Names) (failure : List Stmt) : List Stmt :=
  [.letVar (n 7) (.localVar (n 6)), .ite (.localVar (n 7)) failure [],
   .assignVar (n 1) (.localVar (n 0))]

/-- The decomposition preserves the exact imported statement list. -/
theorem body_split (n : Names) (field member : String) (sentinel : Nat) (failure : List Stmt) :
    body n field member sentinel failure = first n field member ++
      (second n sentinel ++ last n failure) := by rfl

/-- A zero first-stage rejection flag implies increasing registered signers. -/
theorem first_sound (o : DenoteOracle) (fs : List Field) (state after : DenoteState)
    (n : Names) (fresh : Function.Injective n) (field member : String)
    (executed : execStmtList o fs state (first n field member) = .continue after)
    (accepted : lookupValue after.bindings (n 3) = 0) :
    lookupValue state.bindings (n 1) < lookupValue state.bindings (n 0) ∧
    ∃ registered, evalExpr o fs state (.structMember field (.localVar (n 0)) member) =
      some registered ∧ registered ≠ 0 := by
  cases hm : evalExpr o fs state (.structMember field (.localVar (n 0)) member) with
  | none =>
      by_cases order : lookupValue state.bindings (n 0) ≤ lookupValue state.bindings (n 1)
      all_goals simp [first, execStmtList, execStmt, eval_local, eval_le,
        lookup_named n fresh, member_two_temps n fresh, hm, boolWord, order] at executed
      all_goals cases executed; simp [lookup_named n fresh] at accepted
  | some registered =>
      by_cases order : lookupValue state.bindings (n 0) ≤ lookupValue state.bindings (n 1)
      all_goals by_cases empty : registered = 0
      all_goals simp [first, execStmtList, execStmt, eval_local, eval_le, eval_eq, eval_literal,
        lookup_named n fresh, member_two_temps n fresh, hm, boolWord, order, empty] at executed
      all_goals cases executed
      all_goals simp [lookup_named n fresh] at accepted
      exact ⟨by omega, registered, rfl, empty⟩

/-- A zero second-stage rejection flag implies both prior checks and sentinel exclusion. -/
theorem second_sound (o : DenoteOracle) (fs : List Field) (state after : DenoteState)
    (n : Names) (fresh : Function.Injective n) (sentinel : Nat)
    (executed : execStmtList o fs state (second n sentinel) = .continue after)
    (accepted : lookupValue after.bindings (n 6) = 0) :
    lookupValue state.bindings (n 3) = 0 ∧
      lookupValue state.bindings (n 0) ≠ wordNormalize sentinel := by
  by_cases flag : lookupValue state.bindings (n 3) = 0
  all_goals by_cases reserved : lookupValue state.bindings (n 0) = wordNormalize sentinel
  all_goals simp [second, execStmtList, execStmt, eval_local, eval_eq, eval_literal,
    lookup_named n fresh, boolWord, flag, reserved] at executed
  all_goals cases executed
  all_goals simp [lookup_named n fresh, flag] at accepted
  exact ⟨flag, reserved⟩

/-- A successful final stage necessarily passed its rejection branch. -/
theorem last_sound (o : DenoteOracle) (fs : List Field) (state after : DenoteState)
    (n : Names) (fresh : Function.Injective n) (failure : List Stmt)
    (rejects : ∀ s t, execStmtList o fs s failure ≠ .continue t)
    (executed : execStmtList o fs state (last n failure) = .continue after) :
    lookupValue state.bindings (n 6) = 0 ∧
      lookupValue after.bindings (n 1) = lookupValue state.bindings (n 0) := by
  by_cases flag : lookupValue state.bindings (n 6) = 0
  · simp [last, execStmtList, execStmt, eval_local, lookup_named n fresh, flag] at executed
    cases executed
    simp [lookup_named n fresh, flag]
  · simp [last, execStmtList, execStmt, eval_local, lookup_named n fresh, flag] at executed
    generalize h : execStmtList o fs _ failure = result at executed
    cases result <;> simp_all

/-- The first stage changes flags but preserves the signer being checked. -/
theorem first_current (o : DenoteOracle) (fs : List Field) (state after : DenoteState)
    (n : Names) (fresh : Function.Injective n) (field member : String)
    (executed : execStmtList o fs state (first n field member) = .continue after) :
    lookupValue after.bindings (n 0) = lookupValue state.bindings (n 0) := by
  have h := list_frame o fs state (first n field member) [n 0]
    (by simp [first, prefixList, prefixStmt, fresh.eq_iff])
  rw [executed] at h
  exact h.2 (n 0) (by simp)

/-- The sentinel stage also preserves the signer being checked. -/
theorem second_current (o : DenoteOracle) (fs : List Field) (state after : DenoteState)
    (n : Names) (fresh : Function.Injective n) (sentinel : Nat)
    (executed : execStmtList o fs state (second n sentinel) = .continue after) :
    lookupValue after.bindings (n 0) = lookupValue state.bindings (n 0) := by
  have h := list_frame o fs state (second n sentinel) [n 0]
    (by simp [second, prefixList, prefixStmt, fresh.eq_iff])
  rw [executed] at h
  exact h.2 (n 0) (by simp)

/-- Successful execution of the exact lowered guard enforces all three checks. -/
theorem sound (o : DenoteOracle) (fs : List Field) (state after : DenoteState)
    (n : Names) (fresh : Function.Injective n) (field member : String) (sentinel : Nat)
    (failure : List Stmt) (rejects : ∀ s t, execStmtList o fs s failure ≠ .continue t)
    (executed : execStmtList o fs state (body n field member sentinel failure) = .continue after) :
    lookupValue state.bindings (n 1) < lookupValue state.bindings (n 0) ∧
    (∃ registered, evalExpr o fs state (.structMember field (.localVar (n 0)) member) =
      some registered ∧ registered ≠ 0) ∧
    lookupValue state.bindings (n 0) ≠ wordNormalize sentinel ∧
    lookupValue after.bindings (n 1) = lookupValue state.bindings (n 0) := by
  rw [body_split] at executed
  obtain ⟨middle, step₁, rest⟩ := split_prefix_continue o fs state after _ _ executed
  obtain ⟨tail, step₂, step₃⟩ := split_prefix_continue o fs middle after _ _ rest
  have lastFacts := last_sound o fs tail after n fresh failure rejects step₃
  have secondFacts := second_sound o fs middle tail n fresh sentinel step₂ lastFacts.1
  have firstFacts := first_sound o fs state middle n fresh field member step₁ secondFacts.1
  have current₁ := first_current o fs state middle n fresh field member step₁
  have current₂ := second_current o fs middle tail n fresh sentinel step₂
  exact ⟨firstFacts.1, firstFacts.2, by simpa only [current₁] using secondFacts.2,
    lastFacts.2.trans (current₂.trans current₁)⟩

end Compiler.CompilationModel.SolidityImport.OrderedGuard
