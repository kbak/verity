import Lean

/-! A fuel-bounded observer for potentially nonterminating source loops.
Exhaustion is absence of an observation, never a Solidity halt or a successful
continuation. This module does not extend importer admission by itself. -/

namespace Compiler.CompilationModel.SolidityImport.LoopExecution

/-- One source iteration either continues with its state or observes a source
exit. The outcome type retains the caller's distinct return and halt variants. -/
inductive Step (State Outcome : Type) where
  | next (state : State)
  | halt (outcome : Outcome)

/-- A loop body distinguishes fallthrough, continue, break and propagation of an
enclosing return or exceptional halt. State includes every observable body effect. -/
inductive BodyResult (State Outcome : Type) where
  | normal (state : State)
  | continueLoop (state : State)
  | breakLoop (state : State)
  | abrupt (outcome : Outcome)

/-- Leaving the loop normally preserves its final state. An abrupt outcome is
propagated unchanged; transaction rollback belongs to the enclosing evaluator. -/
inductive Exit (State Outcome : Type) where
  | normal (state : State)
  | abrupt (outcome : Outcome)
  deriving BEq, Repr

/-- One while-loop observation, including reevaluation of an effectful condition.
The condition returns its updated state with the Boolean result. A condition halt
propagates directly. `continue` returns to the condition and `break` skips it.
An observation step is not an EVM gas unit. -/
def whileStep {State Outcome : Type}
    (condition : State → Step (Bool × State) Outcome)
    (body : State → BodyResult State Outcome) (state : State) :
    Step State (Exit State Outcome) :=
  match condition state with
  | .halt outcome => .halt (.abrupt outcome)
  | .next (false, nextState) => .halt (.normal nextState)
  | .next (true, nextState) =>
      match body nextState with
      | .normal afterBody | .continueLoop afterBody => .next afterBody
      | .breakLoop afterBody => .halt (.normal afterBody)
      | .abrupt outcome => .halt (.abrupt outcome)

/-- Observe at most `fuel` iteration steps. `none` is instrumentation exhaustion;
it must not be converted to a successful return, INVALID, or REVERT. -/
def execute {State Outcome : Type} (step : State → Step State Outcome) :
    Nat → State → Option Outcome
  | 0, _ => none
  | fuel + 1, state =>
      match step state with
      | .next nextState => execute step fuel nextState
      | .halt outcome => some outcome

/-- A finite source execution, independently of any observer fuel choice. -/
inductive Reaches {State Outcome : Type} (step : State → Step State Outcome) :
    State → Outcome → Prop where
  | halt {state outcome} (h : step state = .halt outcome) : Reaches step state outcome
  | next {state nextState outcome} (h : step state = .next nextState)
      (tail : Reaches step nextState outcome) : Reaches step state outcome

/-- Every observed outcome comes from a finite source execution. -/
theorem execute_sound {State Outcome : Type} (step : State → Step State Outcome)
    {fuel : Nat} {state : State} {outcome : Outcome}
    (h : execute step fuel state = some outcome) : Reaches step state outcome := by
  induction fuel generalizing state with
  | zero => cases h
  | succ fuel ih =>
    cases hs : step state with
    | next nextState =>
      exact Reaches.next hs (ih (by simpa only [execute, hs] using h))
    | halt result =>
      simp only [execute, hs, Option.some.injEq] at h
      subst result
      exact Reaches.halt hs

/-- Every finite source execution is observable with sufficient fuel. -/
theorem reaches_has_fuel {State Outcome : Type} (step : State → Step State Outcome)
    {state : State} {outcome : Outcome} (h : Reaches step state outcome) :
    ∃ fuel, execute step fuel state = some outcome := by
  induction h with
  | halt hs => exact ⟨1, by simp only [execute, hs]⟩
  | next hs _ ih =>
    obtain ⟨fuel, hfuel⟩ := ih
    exact ⟨fuel + 1, by simp only [execute, hs, hfuel]⟩

end Compiler.CompilationModel.SolidityImport.LoopExecution
