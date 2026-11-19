import Compiler.SolidityImport.OrderedSearchWindow

namespace Compiler.CompilationModel.SolidityImport.IntervalSearch.OrderedSearchWindow
open LoopExecution

variable {State Outcome : Type}

/-- Evidence about one actual source path. The exit predicate filters out adapter
errors. Each continuing edge must agree with the independent ordered-key table. -/
inductive CheckedPath (w : OrderedSearchWindow) (step : State → Step State Outcome)
    (low high : State → Nat) (isExit : Outcome → Bool) : State → Prop where
  | exit {s result} (transition : step s = .halt result) (sourceExit : isExit result = true) :
      CheckedPath w step low high isExit s
  | next {s t} (transition : step s = .next t)
      (moves : w.Moves (low s) (high s) (low t) (high t))
      (tail : CheckedPath w step low high isExit t) : CheckedPath w step low high isExit s

/-- A continuing step on a checked path retains its tail and its exact source update. -/
theorem moves_and_tail_of_next {w : OrderedSearchWindow} {step : State → Step State Outcome}
    {low high : State → Nat} {isExit : Outcome → Bool} {s t : State}
    (path : CheckedPath w step low high isExit s) (next : step s = .next t) :
    w.Moves (low s) (high s) (low t) (high t) ∧ CheckedPath w step low high isExit t := by
  cases path with
  | exit transition _ =>
    rw [next] at transition
    contradiction
  | next transition moves tail =>
    rw [next] at transition
    cases transition
    exact ⟨moves, tail⟩

/-- A positive interval shrinks strictly whenever its successor is at most half as wide. -/
theorem width_lt_of_moves (w : OrderedSearchWindow) {pivot low high nextLow nextHigh : Nat}
    (bracket : w.Brackets pivot) (retains : w.Retains pivot low high)
    (moves : w.Moves low high nextLow nextHigh) : nextHigh + 1 - nextLow < high + 1 - low := by
  have shrink := (w.progress_of_moves bracket retains moves).2
  obtain ⟨left, right, _⟩ := retains
  omega

instance (w : OrderedSearchWindow) (low high nextLow nextHigh : Nat) :
    Decidable (w.Moves low high nextLow nextHigh) := by
  unfold Moves
  infer_instance

/-- Construct a kernel-checkable certificate for a concrete starting frame. Compare every
actual continuing edge to the independent table and stop at a genuine source exit.
Recursion is justified by interval width, without a caller-selected observation budget. -/
def checkPath (w : OrderedSearchWindow) (step : State → Step State Outcome)
    (low high : State → Nat) (isExit : Outcome → Bool) (pivot : Nat)
    (bracket : w.Brackets pivot) (s : State) (retains : w.Retains pivot (low s) (high s)) :
    Option (PLift (CheckedPath w step low high isExit s)) :=
  match transition : step s with
  | .halt result =>
    if h : isExit result = true then some ⟨.exit transition h⟩ else none
  | .next t =>
    if moves : w.Moves (low s) (high s) (low t) (high t) then
      (checkPath w step low high isExit pivot bracket t
        (w.progress_of_moves bracket retains moves).1).map
          fun tail => ⟨.next transition moves tail.down⟩
    else none
termination_by high s + 1 - low s
decreasing_by exact w.width_lt_of_moves bracket retains moves

end Compiler.CompilationModel.SolidityImport.IntervalSearch.OrderedSearchWindow
