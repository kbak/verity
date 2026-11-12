import Verity.Core.Model.Denote
/-! Typed callback completion preserves the original-bytecode gas cursor on all exits. -/
namespace Compiler.CompilationModel.Denote
open ByteExternalCall

/-- Failure forwards all bytes and retains the consumed meter without a world. -/
theorem finish_void_failure (state : DenoteState)
    (observed : Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) (failed : observed.success = false) :
    finishLegacyVoidCall state observed meter =
      (.revertWithData observed.returndata, observed.touched, meter) := by
  simp only [finishLegacyVoidCall, failed, Bool.not_false, ↓reduceIte]

/-- Every completion returns the exact accounted gas cursor. -/
theorem finish_void_meter (state : DenoteState)
    (observed : Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) :
    (finishLegacyVoidCall state observed meter).2.2 = meter := by
  cases success : observed.success <;>
    simp only [finishLegacyVoidCall, success, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]

/-- Successful continuation installs the accounted gas cursor in canonical Denote. -/
theorem finish_void_success_gas (state : DenoteState)
    (observed : Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) (succeeded : observed.success = true) :
    match (finishLegacyVoidCall state observed meter).1 with
    | .continue after => after.sourceGas = meter
    | _ => False := by
  simp only [finishLegacyVoidCall, succeeded, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- The functional and gas-observing adapters share one execution result. -/
theorem execute_void_of_observed (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (mod : Compiler.ECM.ExternalCallModule) (selector : Nat)
    (layout : List Compiler.Yul.LegacyVoidCalls.Argument) (args : List Expr)
    (site : Option String) (outcome : StmtOutcome) (touched : List Verity.StorageKey)
    (meter : Option SourceGas.State)
    (executed : executeLegacyVoidCallObserved oracle fields state mod selector layout args site =
      .ok (outcome, touched, meter)) :
    executeLegacyVoidCall oracle fields state mod selector layout args site =
      .ok (outcome, touched) := by
  simp only [executeLegacyVoidCall, executed]
  rfl
/-- Pin the metered transport to its canonical functional execution arm. -/
theorem exec_stmt_void_gas_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (selector : Nat)
    (layout : List Compiler.Yul.LegacyVoidCalls.Argument) (args : List Expr) (site : String) :
    execStmt oracle fields state
        (.ecm (Compiler.ECM.LegacyVoidCall.module selector layout (some site)) args) =
      (match executeLegacyVoidCall oracle fields state
          (Compiler.ECM.LegacyVoidCall.module selector layout (some site))
          selector layout args (some site) with
       | .ok (outcome, _) => outcome
       | .error _ => .revert) := by
  rfl
end Compiler.CompilationModel.Denote
