import Verity.Core.Model.Denote

/-! Meter attachment preserves static-call results and retains gas on terminal failure. -/
namespace Compiler.CompilationModel.Denote

/-- Successful meter attachment changes only the gas cursor. -/
theorem finish_source_static_continue (state : DenoteState)
    (touched : List Verity.StorageKey) (meter : SourceGas.State) :
    finishSourceStaticCall (.ok (.continue state, touched)) meter =
      .ok (.continue { state with sourceGas := some meter }, touched, some meter) := by
  rfl

/-- Failed callbacks keep exact revert bytes and the already consumed meter. -/
theorem finish_source_static_revert (data : ByteExternalCall.Bytes)
    (touched : List Verity.StorageKey) (meter : SourceGas.State) :
    finishSourceStaticCall (.ok (.revertWithData data, touched)) meter =
      .ok (.revertWithData data, touched, some meter) := by
  rfl

/-- Every successful adapter result retains precisely its supplied meter. -/
theorem finish_source_static_meter
    (result : Except String (StmtOutcome × List Verity.StorageKey))
    (meter : SourceGas.State) (outcome : StmtOutcome) (touched : List Verity.StorageKey)
    (observed : Option SourceGas.State)
    (executed : finishSourceStaticCall result meter = .ok (outcome, touched, observed)) :
    observed = some meter := by
  cases result with
  | error message =>
      change Except.error message = Except.ok (outcome, touched, observed) at executed
      cases executed
  | ok pair =>
      have projected := congrArg (fun value => value.toOption.map (fun row => row.2.2)) executed
      change some (some meter) = some observed at projected
      exact (Option.some.inj projected).symm

/-- Canonical and gas-observing execution share one checked static-call result. -/
theorem execute_source_static_of_observed (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (mod : Compiler.ECM.ExternalCallModule) (result : String)
    (kind : Compiler.ECM.LegacyStaticKind) (site : String) (args : List Expr)
    (outcome : StmtOutcome) (touched : List Verity.StorageKey) (meter : Option SourceGas.State)
    (executed : executeSourceStaticCallObserved oracle fields state mod result kind site args =
      .ok (outcome, touched, meter)) :
    executeSourceStaticCall oracle fields state mod result kind site args =
      .ok (outcome, touched) := by
  simp only [executeSourceStaticCall, executed]
  rfl

/-- Pin source-gas static metadata to the canonical interpreter arm. -/
theorem exec_stmt_source_static_arm (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (result : String) (kind : Compiler.ECM.LegacyStaticKind)
    (site : String) (args : List Expr) :
    execStmt oracle fields state
      (.ecm (Compiler.ECM.SourceStaticCall.module result kind site) args) =
      (match executeSourceStaticCall oracle fields state
          (Compiler.ECM.SourceStaticCall.module result kind site) result kind site args with
       | .ok (outcome, _) => outcome
       | .error _ => .revert) := by
  rfl

end Compiler.CompilationModel.Denote
