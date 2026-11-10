import Compiler.SolidityImport.SignatureCallFrames

namespace Compiler.CompilationModel.SolidityImport.AuthorizationFrames
open Denote

/-- A frame composes through a continuing intermediate state. -/
theorem frame_trans (key : String) (before middle : DenoteState) (outcome : StmtOutcome)
    (first : BindingFrame key before (.continue middle))
    (second : BindingFrame key middle outcome) : BindingFrame key before outcome := by
  cases outcome <;> simp only [BindingFrame] at *
  · exact ⟨second.1.trans first.1, second.2.trans first.2⟩

/-- Empty-revert memory transport cannot return or continue successfully. -/
theorem revert_frame (o : DenoteOracle) (fs : List Field) (state : DenoteState)
    (mod : Compiler.ECM.ExternalCallModule) (args : List Expr) (key : String) :
    match executeByteRevertMemory o fs state mod args with
    | .error _ => True
    | .ok outcome => BindingFrame key state outcome := by
  unfold executeByteRevertMemory
  cases evalExprList o fs state args with
  | none => split_ifs <;> trivial
  | some values =>
      rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        split_ifs <;> trivial

/-- The actual bounded executor preserves an untouched binding, including its index bind. -/
theorem loop_frame (key indexVar : String) (runBody : DenoteState → StmtOutcome)
    (different : indexVar ≠ key)
    (bodyFrame : ∀ state, BindingFrame key state (runBody state))
    (state : DenoteState) (index remaining : Nat) :
    BindingFrame key state (execForEachLoop indexVar runBody state index remaining) := by
  induction remaining generalizing state index with
  | zero => exact ⟨rfl, rfl⟩
  | succ remaining ih =>
      let bound :=
        { state with bindings := bindValue state.bindings indexVar (wordNormalize index) }
      have indexFrame : BindingFrame key state (.continue bound) :=
        ⟨lookup_bind_other _ _ _ _ different, rfl⟩
      have body := frame_trans key state bound _ indexFrame (bodyFrame bound)
      simp only [execForEachLoop]
      cases h : runBody bound with
      | «continue» next =>
          exact frame_trans key state next _ (by simpa [h] using body) (ih next (index + 1))
      | stop next => simp [h, BindingFrame] at body
      | «return» value next => simp [h, BindingFrame] at body
      | revert => trivial
      | revertWithData bytes => trivial
      | invalid => trivial

/-- The count evaluation and initial loop-index binding preserve the frame. -/
theorem foreach_frame (o : DenoteOracle) (fs : List Field) (state : DenoteState)
    (key index : String) (count : Expr) (body : List Stmt) (different : index ≠ key)
    (bodyFrame : ∀ s, BindingFrame key s (execStmtList o fs s body)) :
    BindingFrame key state (execStmt o fs state (.forEach index count body)) := by
  cases h : evalExpr o fs state count with
  | none => simp [execStmt, h, BindingFrame]
  | some bound =>
      let initial := { state with bindings := bindValue state.bindings index (wordNormalize 0) }
      have first : BindingFrame key state (.continue initial) :=
        ⟨lookup_bind_other _ _ _ _ different, rfl⟩
      simpa only [execStmt, h] using frame_trans key state initial _ first
        (loop_frame key index _ different bodyFrame initial 0 bound)

/-- A require either preserves the complete state or rejects. -/
theorem require_frame (o : DenoteOracle) (fs : List Field) (state : DenoteState)
    (key : String) (condition : Expr) (message : String) :
    BindingFrame key state (execStmt o fs state (.require condition message)) := by
  cases h : evalExpr o fs state condition with
  | none => simp only [execStmt, h, BindingFrame]
  | some value =>
      simp only [execStmt, h]
      split <;> simp only [BindingFrame, and_self]

mutual
/-- Checked read-only control-flow fragment with a protected local. Other effects fail closed. -/
def protectedStmt (key : String) : Stmt → Bool
  | .letVar name _ | .assignVar name _ => decide (name ≠ key)
  | .mstore _ _ | .panic _ | .revertEmpty | .revertReturndata | .require _ _ => true
  | .ite _ yes no => protectedList key yes && protectedList key no
  | .forEach index _ body => decide (index ≠ key) && protectedList key body
  | .ecm mod _ => match mod.byteTransport with
    | some (.legacyRecover result) | some (.legacyBytes4 result _) => decide (result ≠ key)
    | some .revertMemory | some .invalid => true
    | _ => false
  | _ => false
/-- All instructions must belong to the closed fragment. -/
def protectedList (key : String) : List Stmt → Bool
  | [] => true
  | stmt :: rest => protectedStmt key stmt && protectedList key rest
end

/-- Checked-call instrumentation errors become reverting interpreter outcomes. -/
theorem call_frame_outcome (key : String) (state : DenoteState)
    (result : Except String (StmtOutcome × List Verity.StorageKey)) :
    CallFrame key state result →
    BindingFrame key state
      (match result with | .ok (outcome, _) => outcome | .error _ => .revert) := by
  intro h
  cases result with
  | error message => trivial
  | ok pair => exact h

/-- A closed legacy call has only its documented result binding as a local effect. -/
theorem ecm_frame (o : DenoteOracle) (fs : List Field) (state : DenoteState)
    (mod : Compiler.ECM.ExternalCallModule) (args : List Expr) (key : String)
    (accepted : protectedStmt key (.ecm mod args) = true) :
    BindingFrame key state (execStmt o fs state (.ecm mod args)) := by
  cases transport : mod.byteTransport with
  | none => simp [protectedStmt, transport] at accepted
  | some transportValue =>
      cases transportValue <;> simp [protectedStmt, transport] at accepted
      case legacyRecover result =>
        have h := legacy_call_frame o fs state mod result key none args accepted
        simp only [execStmt, transport]
        exact call_frame_outcome key state _ h
      case legacyBytes4 result selector =>
        have h := legacy_call_frame o fs state mod result key (some selector) args accepted
        simp only [execStmt, transport]
        exact call_frame_outcome key state _ h
      case invalid =>
        simp only [execStmt, transport]
        split <;> trivial
      case revertMemory =>
        have h := revert_frame o fs state mod args key
        simp only [execStmt, transport]
        cases result : executeByteRevertMemory o fs state mod args with
        | error message => trivial
        | ok outcome => simpa only [result] using h

mutual
/-- The structural certificate implies the actual interpreter frame and rules out early success. -/
theorem protected_stmt_frame (o : DenoteOracle) (fs : List Field) (state : DenoteState)
    (stmt : Stmt) (key : String) (accepted : protectedStmt key stmt = true) :
    BindingFrame key state (execStmt o fs state stmt) := by
  unfold protectedStmt at accepted
  split at accepted
  · rename_i name value
    cases h : evalExpr o fs state value <;> simp [execStmt, h, BindingFrame]
    exact lookup_bind_other _ _ _ _ (of_decide_eq_true accepted)
  · rename_i name value
    cases h : evalExpr o fs state value <;> simp [execStmt, h, BindingFrame]
    exact lookup_bind_other _ _ _ _ (of_decide_eq_true accepted)
  · rename_i offset value
    cases ho : evalExpr o fs state offset <;> cases hv : evalExpr o fs state value <;>
      simp [execStmt, ho, hv, BindingFrame]
  · trivial
  · trivial
  · trivial
  · exact require_frame o fs state key _ _
  · rename_i condition yes no
    obtain ⟨hy, hn⟩ := Bool.and_eq_true_iff.mp accepted
    cases h : evalExpr o fs state condition <;> simp only [execStmt, h]
    · trivial
    · split
      · exact protected_list_frame o fs state yes key hy
      · exact protected_list_frame o fs state no key hn
  · rename_i index count body
    obtain ⟨different, hb⟩ := Bool.and_eq_true_iff.mp accepted
    exact foreach_frame o fs state key index count body (of_decide_eq_true different)
      (fun s => protected_list_frame o fs s body key hb)
  · exact ecm_frame o fs state _ _ key accepted
  · cases accepted
/-- List composition retains both protected locals and the no-early-success guarantee. -/
theorem protected_list_frame (o : DenoteOracle) (fs : List Field) (state : DenoteState)
    (body : List Stmt) (key : String) (accepted : protectedList key body = true) :
    BindingFrame key state (execStmtList o fs state body) := by
  cases body with
  | nil => exact ⟨rfl, rfl⟩
  | cons stmt rest =>
      obtain ⟨hs, hr⟩ := Bool.and_eq_true_iff.mp accepted
      have first := protected_stmt_frame o fs state stmt key hs
      simp only [execStmtList]
      cases h : execStmt o fs state stmt with
      | «continue» next =>
          exact frame_trans key state next _ (by simpa [h] using first)
            (protected_list_frame o fs next rest key hr)
      | stop next => simp [h, BindingFrame] at first
      | «return» value next => simp [h, BindingFrame] at first
      | revert => trivial
      | revertWithData bytes => trivial
      | invalid => trivial
end
end Compiler.CompilationModel.SolidityImport.AuthorizationFrames

namespace Compiler.CompilationModel.SolidityImport.AuthorizationFrames
open Denote

/-- Closed memory reverts cannot continue, even when metadata or argument reads are invalid. -/
theorem memory_revert_no_continue (o : DenoteOracle) (fields : List Field)
    (state after : DenoteState)
    (mod : Compiler.ECM.ExternalCallModule) (args : List Expr)
    (transport : mod.byteTransport = some .revertMemory) :
    execStmt o fields state (.ecm mod args) ≠ .continue after := by
  simp only [execStmt, transport]
  unfold executeByteRevertMemory
  cases evalExprList o fields state args with
  | none => split_ifs <;> simp [bind, Except.bind, pure, Except.pure, throw, throwThe]
  | some values =>
      rcases values with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        split_ifs <;> simp [bind, Except.bind, pure, Except.pure, throw, throwThe]

/-- Prefix instructions cannot turn a noncontinuing suffix into a continuation. -/
theorem append_no_continue (o : DenoteOracle) (fields : List Field) (pre suffix : List Stmt)
    (rejects : ∀ state after, execStmtList o fields state suffix ≠ .continue after)
    (state after : DenoteState) :
    execStmtList o fields state (pre ++ suffix) ≠ .continue after := by
  rw [exec_append]
  cases execStmtList o fields state pre with
  | «continue» next => exact rejects next after
  | stop next => simp
  | «return» value next => simp
  | revert => simp
  | revertWithData bytes => simp
  | invalid => simp

/-- Revert payload construction followed by the closed revert transport always rejects. -/
theorem ends_memory_revert (o : DenoteOracle) (fields : List Field) (pre : List Stmt)
    (mod : Compiler.ECM.ExternalCallModule) (args : List Expr)
    (transport : mod.byteTransport = some .revertMemory) (state after : DenoteState) :
    execStmtList o fields state (pre ++ [.ecm mod args]) ≠ .continue after := by
  apply append_no_continue o fields pre [_]
  intro before final
  rw [exec_singleton]
  exact memory_revert_no_continue o fields before final mod args transport

end Compiler.CompilationModel.SolidityImport.AuthorizationFrames
