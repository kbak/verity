import Verity.Core.Model.Denote
/-! Frame laws for raw STATICCALL before source-level copying and decoding. -/
namespace Compiler.CompilationModel.Denote
/-- Checked static calls preserve the whole world, including exceptional exits. -/
theorem checked_static_world (adversary : ByteExternalCall.Adversary
    Verity.ContractState Verity.StorageKey) (request : ByteExternalCall.Request)
    (before : Verity.ContractState)
    (observed : ByteExternalCall.Observation Verity.ContractState Verity.StorageKey)
    (kind : request.kind = .staticcall)
    (executed : ByteExternalCall.executeChecked adversary request before = .ok observed) :
    observed.world = before := by
  cases accepted : adversary.accepts request before with
  | false =>
      rw [ByteExternalCall.executeChecked_rejects _ _ _ accepted] at executed
      cases executed
  | true =>
      rw [ByteExternalCall.executeChecked_agrees _ _ _ accepted] at executed
      cases executed
      exact ByteExternalCall.execute_static_world adversary request before kind
/-- Completing a checked static response preserves the caller's world. -/
theorem finish_raw_static_world (state : DenoteState) (result : String)
    (observed : ByteExternalCall.Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) (frame : observed.world = state.world) :
    (finishRawStaticCall state result observed meter).world = state.world := by
  exact frame
/-- All bytes are retained on both success and failure, without decoding. -/
theorem finish_raw_static_bytes (state : DenoteState) (result : String)
    (observed : ByteExternalCall.Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) :
    (finishRawStaticCall state result observed meter).rawReturndata =
      some observed.returndata := by
  rfl
/-- Child failure is a false binding, not an automatic terminal revert. -/
theorem finish_raw_static_failure (state : DenoteState) (result : String)
    (observed : ByteExternalCall.Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) (failed : observed.success = false) :
    (finishRawStaticCall state result observed meter).bindings =
      bindValue state.bindings result 0 := by
  simp only [finishRawStaticCall, failed, Bool.false_eq_true, if_false]
/-- Completion retains the accounted meter even when the child failed. -/
theorem finish_raw_static_meter (state : DenoteState) (result : String)
    (observed : ByteExternalCall.Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) :
    (finishRawStaticCall state result observed meter).sourceGas = meter := by
  rfl
/-- Pin the closed raw transport to canonical execution. -/
theorem exec_stmt_raw_static_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (result : String) (args : List Expr) :
    execStmt oracle fields state (.ecm (Compiler.ECM.SolidityRawStaticCall.module result) args) =
      (match executeRawStaticCall oracle fields state
          (Compiler.ECM.SolidityRawStaticCall.module result) result args with
       | .ok (outcome, _) => outcome
       | .error _ => .revert) := by
  rfl
end Compiler.CompilationModel.Denote
