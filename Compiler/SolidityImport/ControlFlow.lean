import Compiler.SolidityImport.LoopExecution

/-! Structured control flow for observed executions. This representation retains
unbounded loops; the observer's fuel is not part of the imported source program. -/

namespace Compiler.CompilationModel.SolidityImport.ControlFlow
open LoopExecution

/-- Structured statements around an existing leaf statement and expression language.
Condition preludes execute on every test. A loop's postlude executes after normal
body completion and continue, but never after break or an abrupt exit. -/
inductive Program (Atom Condition : Type) where
  | atom (statement : Atom)
  | branch (prelude : List Atom) (condition : Condition)
      (yes no : List (Program Atom Condition))
  | loop (prelude : List Atom) (condition : Condition)
      (body postlude : List (Program Atom Condition))
  | breakLoop
  | continueLoop
  | call (name : String) (results : List String) (body : List (Program Atom Condition))
  | leaveCall
  deriving Repr

/-- Explicit continuations retain the nearest loop boundary across nested blocks. -/
inductive Frame (Atom Condition : Type) where
  | code (statements : List (Program Atom Condition))
  | branch (condition : Condition) (yes no : List (Program Atom Condition))
  | test (prelude : List Atom) (condition : Condition)
      (body postlude : List (Program Atom Condition))
  | boundary (prelude : List Atom) (condition : Condition)
      (body postlude : List (Program Atom Condition))
  | callBoundary

/-- Interpreter state includes pending control flow as well as the source state. -/
structure Machine (Atom Condition State : Type) where
  frames : List (Frame Atom Condition)
  state : State

/-- Leave only the nearest enclosing loop. Continue retains its postlude and next
test; break discards both. An unbound control transfer is unsupported, not a revert. -/
def transfer {Atom Condition : Type} (isContinue : Bool) :
    List (Frame Atom Condition) → Except String (List (Frame Atom Condition))
  | [] => .error "loop control outside a loop"
  | .boundary pre cond body post :: rest => .ok <|
      if isContinue then .code post :: .code [.loop pre cond body post] :: rest else rest
  | .callBoundary :: _ => .error "loop control crosses a helper boundary"
  | _ :: rest => transfer isContinue rest

/-- A helper return skips its loops and pending statements, retaining the caller. -/
def leave {Atom Condition : Type} :
    List (Frame Atom Condition) → Except String (List (Frame Atom Condition))
  | [] => .error "helper return outside a helper"
  | .callBoundary :: rest => .ok rest
  | _ :: rest => leave rest

/-- Execute one control-machine transition using the existing leaf semantics.
Unsupported leaf/condition evaluation remains an error, separate from source exits. -/
def step {Atom Condition State Outcome : Type}
    (leaf : Atom → State → Except String (BodyResult State Outcome))
    (test : Condition → State → Except String (Bool × State))
    (machine : Machine Atom Condition State) :
    Step (Machine Atom Condition State) (Except String (Exit State Outcome)) := Id.run do
  let state := machine.state
  let next frames state := Step.next ({ frames, state } : Machine Atom Condition State)
  let done outcome := Step.halt (.ok outcome)
  match machine.frames with
  | [] => return done (.normal state)
  | .code [] :: rest => return next rest state
  | .code (Program.atom statement :: tail) :: rest =>
      match leaf statement state with
      | .error error => return .halt (.error error)
      | .ok (.normal afterBody) => return next (.code tail :: rest) afterBody
      | .ok (.abrupt outcome) => return done (.abrupt outcome)
      | .ok _ => return .halt (.error "leaf statement returned structured loop control")
  | .code (.branch pre cond yes no :: tail) :: rest =>
      return next (.code (pre.map Program.atom) :: .branch cond yes no :: .code tail :: rest) state
  | .code (.loop pre cond body post :: tail) :: rest =>
      return next (.code (pre.map Program.atom) :: .test pre cond body post ::
        .code tail :: rest) state
  | .code (.breakLoop :: _) :: rest =>
      match transfer false rest with
      | .ok frames => return next frames state
      | .error error => return .halt (.error error)
  | .code (.continueLoop :: _) :: rest =>
      match transfer true rest with
      | .ok frames => return next frames state
      | .error error => return .halt (.error error)
  | .code (.call _ _ body :: tail) :: rest =>
      return next (.code body :: .callBoundary :: .code tail :: rest) state
  | .code (.leaveCall :: _) :: rest =>
      match leave rest with
      | .ok frames => return next frames state
      | .error error => return .halt (.error error)
  | .callBoundary :: rest => return next rest state
  | .branch cond yes no :: rest =>
      match test cond state with
      | .error error => return .halt (.error error)
      | .ok (takeYes, afterTest) =>
          return next (.code (if takeYes then yes else no) :: rest) afterTest
  | .test pre cond body post :: rest =>
      match test cond state with
      | .error error => return .halt (.error error)
      | .ok (true, afterTest) =>
          return next (.code body :: .boundary pre cond body post :: rest) afterTest
      | .ok (false, afterTest) => return next rest afterTest
  | .boundary pre cond body post :: rest =>
      return next (.code post :: .code [.loop pre cond body post] :: rest) state

/-- Observe a program with a global transition budget. `none` means no completed
observation; it must never be encoded as a successful or failed Solidity transaction. -/
def observe {Atom Condition State Outcome : Type}
    (leaf : Atom → State → Except String (BodyResult State Outcome))
    (test : Condition → State → Except String (Bool × State))
    (fuel : Nat) (program : List (Program Atom Condition)) (state : State) :
    Option (Except String (Exit State Outcome)) :=
  execute (step leaf test) fuel { frames := [.code program], state }

end Compiler.CompilationModel.SolidityImport.ControlFlow
