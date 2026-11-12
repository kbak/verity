import Compiler.SolidityImport.TransportBarriers
import Verity.Core.Model.Denote

/-! Non-memory frame soundness for the exact post-call loop admission rule. -/
namespace Compiler.CompilationModel.SolidityImport
open Compiler.CompilationModel.Denote
/-- Forget local bindings and memory, retaining every other observable component. -/
def memoryFrameView (state : DenoteState) : DenoteState :=
  { state with bindings := [], world := { state.world with
    memory := fun _ => 0, byteMemory := DenoteMemory.Memory.empty } }
/-- State-carrying outcomes retain the entire non-memory view. Failed executions
have no successor state; rollback remains a separate transaction property. -/
def preservesNonMemory (before : DenoteState) : StmtOutcome → Prop
  | .continue after | .stop after | .return _ after =>
      memoryFrameView after = memoryFrameView before
  | .revert | .revertWithData _ | .invalid => True

theorem memory_frame_bind (state : DenoteState) (name : String) (value : Nat) :
    memoryFrameView { state with bindings := bindValue state.bindings name value } =
      memoryFrameView state := by
  rfl

theorem memory_frame_store (state : DenoteState) (offset value : Nat) :
    memoryFrameView { state with world :=
      state.world.writePhysicalMemoryValue offset (Verity.Core.Uint256.ofNat value) } =
      memoryFrameView state := by
  rfl

theorem preserves_non_memory_of_view (before after : DenoteState) (outcome : StmtOutcome)
    (same : memoryFrameView after = memoryFrameView before)
    (frame : preservesNonMemory after outcome) : preservesNonMemory before outcome := by
  cases outcome <;> simp only [preservesNonMemory] at frame ⊢
  all_goals first | exact frame.trans same | trivial

theorem exec_local_non_memory (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (value : Expr) :
    preservesNonMemory state (execStmt oracle fields state (.letVar name value)) ∧
    preservesNonMemory state (execStmt oracle fields state (.assignVar name value)) := by
  cases evaluated : evalExpr oracle fields state value <;>
    simp only [execStmt, evaluated, preservesNonMemory, memory_frame_bind, and_self]
  all_goals trivial

theorem exec_mstore_non_memory (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (offset value : Expr) :
    preservesNonMemory state (execStmt oracle fields state (.mstore offset value)) := by
  cases offsetValue : evalExpr oracle fields state offset <;>
    cases storedValue : evalExpr oracle fields state value <;>
    simp only [execStmt, offsetValue, storedValue, preservesNonMemory]
  all_goals first | rfl | trivial

theorem exec_loop_non_memory (name : String) (runBody : DenoteState → StmtOutcome)
    (step : ∀ state, preservesNonMemory state (runBody state))
    (remaining index : Nat) (state : DenoteState) :
    preservesNonMemory state (execForEachLoop name runBody state index remaining) := by
  induction remaining generalizing index state with
  | zero => rfl
  | succ remaining ih =>
      let entered :=
        { state with bindings := bindValue state.bindings name (wordNormalize index) }
      have headFrame := step entered
      simp only [execForEachLoop]
      cases executed : runBody entered with
      | «continue» after =>
          have same : memoryFrameView after = memoryFrameView state := by
            simpa only [executed, preservesNonMemory, entered, memory_frame_bind] using headFrame
          exact preserves_non_memory_of_view state after _ same (ih (index + 1) after)
      | stop after =>
          simpa only [executed, preservesNonMemory, entered, memory_frame_bind] using headFrame
      | «return» value after =>
          simpa only [executed, preservesNonMemory, entered, memory_frame_bind] using headFrame
      | revert => trivial
      | revertWithData bytes => trivial
      | invalid => trivial

theorem exec_ite_non_memory (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (condition : Expr) (yes no : List Stmt)
    (hy : preservesNonMemory state (execStmtList oracle fields state yes))
    (hn : preservesNonMemory state (execStmtList oracle fields state no)) :
    preservesNonMemory state (execStmt oracle fields state (.ite condition yes no)) := by
  cases evaluated : evalExpr oracle fields state condition with
  | none => simp only [execStmt, evaluated, preservesNonMemory]
  | some value =>
      by_cases nonzero : value != 0
      · simpa only [execStmt, evaluated, nonzero, Bool.false_eq_true, ↓reduceIte] using hy
      · simpa only [execStmt, evaluated, nonzero, Bool.false_eq_true, ↓reduceIte] using hn

theorem exec_for_each_non_memory (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (count : Expr) (body : List Stmt)
    (frame : ∀ before, preservesNonMemory before (execStmtList oracle fields before body)) :
    preservesNonMemory state (execStmt oracle fields state (.forEach name count body)) := by
  cases evaluated : evalExpr oracle fields state count with
  | none => simp only [execStmt, evaluated, preservesNonMemory]
  | some bound =>
      have result := exec_loop_non_memory name
        (fun before => execStmtList oracle fields before body) frame bound 0
        { state with bindings := bindValue state.bindings name (wordNormalize 0) }
      exact preserves_non_memory_of_view state _ _ (memory_frame_bind _ _ _)
        (by simpa only [execStmt, evaluated] using result)

mutual
/-- Every admitted memory-only statement preserves all non-memory state. -/
theorem post_call_memory_stmt_frame (oracle : DenoteOracle) (fields : List Field)
    (statement : Stmt) (covered : postCallMemoryStmt statement = true) (state : DenoteState) :
    preservesNonMemory state (execStmt oracle fields state statement) := by
  cases statement <;>
    simp only [postCallMemoryStmt, Bool.and_eq_true, Bool.false_eq_true] at covered
  case letVar name value => exact (exec_local_non_memory oracle fields state name value).1
  case assignVar name value => exact (exec_local_non_memory oracle fields state name value).2
  case mstore offset value => exact exec_mstore_non_memory oracle fields state offset value
  case ite condition yes no =>
    exact exec_ite_non_memory oracle fields state condition yes no
      (post_call_memory_list_frame oracle fields yes covered.1.2 state)
      (post_call_memory_list_frame oracle fields no covered.2 state)
  case forEach name count body =>
    exact exec_for_each_non_memory oracle fields state name count body
      (fun before => post_call_memory_list_frame oracle fields body covered.2 before)

/-- The exact recursive loop-body predicate composes the same frame through execution. -/
theorem post_call_memory_list_frame (oracle : DenoteOracle) (fields : List Field)
    (statements : List Stmt) (covered : postCallMemoryList statements = true)
    (state : DenoteState) :
    preservesNonMemory state (execStmtList oracle fields state statements) := by
  cases statements with
  | nil => rfl
  | cons statement rest =>
      have parts : postCallMemoryStmt statement = true ∧ postCallMemoryList rest = true := by
        simpa only [postCallMemoryList, Bool.and_eq_true] using covered
      have headFrame := post_call_memory_stmt_frame oracle fields statement parts.1 state
      simp only [execStmtList]
      cases executed : execStmt oracle fields state statement with
      | «continue» after =>
          have same : memoryFrameView after = memoryFrameView state := by
            simpa only [executed, preservesNonMemory] using headFrame
          exact preserves_non_memory_of_view state after _ same
            (post_call_memory_list_frame oracle fields rest parts.2 after)
      | stop after => simpa only [executed, preservesNonMemory] using headFrame
      | «return» value after => simpa only [executed, preservesNonMemory] using headFrame
      | revert => trivial
      | revertWithData bytes => trivial
      | invalid => trivial
end
end Compiler.CompilationModel.SolidityImport
