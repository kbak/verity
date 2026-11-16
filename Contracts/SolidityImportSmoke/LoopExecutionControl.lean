import Compiler.SolidityImport.LoopExecution

/-! Executable controls for the generic observer. These do not establish
Solidity importer admission, loop termination, or source/compiler correspondence. -/

open Compiler.CompilationModel.SolidityImport.LoopExecution

private structure LoopState where
  index : Nat := 0
  conditionEffects : Nat := 0
  bodyEffects : Nat := 0
  accumulator : Int := 0
  deriving BEq, Repr

private inductive Outcome where
  | returned (value : Int)
  | reverted
  | invalid
  deriving BEq, Repr

private def condition (limit : Nat) (state : LoopState) : Step (Bool × LoopState) Outcome :=
  .next (state.index < limit, { state with conditionEffects := state.conditionEffects + 1 })

private def body (skip stop : Nat) (state : LoopState) : BodyResult LoopState Outcome := Id.run do
  let state := { state with index := state.index + 1, bodyEffects := state.bodyEffects + 1 }
  if state.index == skip then return .continueLoop state
  let state := { state with accumulator := state.accumulator - 2 }
  if state.index == stop then return .breakLoop state
  return .normal state

private def check (label : String) (actual expected : Option (Exit LoopState Outcome)) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"{label}: expected {repr expected}, got {repr actual}")

/-- Exercise observable control-flow effects and keep resource limits out of source outcomes. -/
def main : IO Unit := do
  let start : LoopState := {}
  check "zero body iterations, condition effect retained"
    (execute (whileStep (condition 0) (body 0 0)) 1 start)
    (some (.normal { conditionEffects := 1 }))
  check "one body iteration and final condition"
    (execute (whileStep (condition 1) (body 0 0)) 2 start)
    (some (.normal { index := 1, conditionEffects := 2, bodyEffects := 1, accumulator := -2 }))
  check "continue skips remaining body; break skips next condition"
    (execute (whileStep (condition 5) (body 2 4)) 4 start)
    (some (.normal { index := 4, conditionEffects := 4, bodyEffects := 4, accumulator := -6 }))
  check "continue takes precedence over a later break"
    (execute (whileStep (condition 3) (body 2 2)) 4 start)
    (some (.normal { index := 3, conditionEffects := 4, bodyEffects := 3, accumulator := -4 }))
  check "zero fuel cannot observe even a false condition"
    (execute (whileStep (condition 0) (body 0 0)) 0 start) none
  check "body completion does not imply condition exit"
    (execute (whileStep (condition 1) (body 0 0)) 1 start) none
  check "repeating state remains unobserved"
    (execute (whileStep (fun s => .next (true, s)) BodyResult.continueLoop) 32 start) none
  for outcome in [Outcome.returned (-7), .reverted, .invalid] do
    check "body abrupt outcome remains distinct"
      (execute (whileStep (condition 1) (fun _ => .abrupt outcome)) 1 start)
      (some (.abrupt outcome))
    check "condition abrupt outcome skips body"
      (execute (whileStep (fun _ => .halt outcome) (body 0 0)) 1 start)
      (some (.abrupt outcome))
  IO.println "loop observer controls passed"
