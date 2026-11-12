import Compiler.SolidityImport.RawStaticCallFrames
import Compiler.SolidityImport.TypedCallGasFrames
import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.Transactions
/-! Composing closed callbacks, subsequent static observations and parent rollback.
These laws assume an admitted child adversary; they do not prove callee code correspondence. -/
namespace Compiler.CompilationModel.SolidityImport.PostCallStaticFrames
open Denote ByteExternalCall

/-- Checked responses are computed from exactly the supplied world. -/
theorem checked_response_current_world
    (adversary : Adversary Verity.ContractState Verity.StorageKey) (request : Request)
    (world : Verity.ContractState) (observed : Observation Verity.ContractState Verity.StorageKey)
    (executed : executeChecked adversary request world = .ok observed) :
    observed.returndata = (adversary.respond request world).returndata := by
  cases accepted : adversary.accepts request world with
  | false =>
      rw [executeChecked_rejects _ _ _ accepted] at executed
      cases executed
  | true =>
      rw [executeChecked_agrees _ _ _ accepted] at executed
      cases executed
      rfl

/-- Successful callback completion installs the child world. -/
theorem finish_void_success_world (state : DenoteState)
    (observed : Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) (succeeded : observed.success = true) :
    match (finishLegacyVoidCall state observed meter).1 with
    | .continue after => after.world = observed.world
    | _ => False := by
  simp only [finishLegacyVoidCall, succeeded, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

/-- A static query after callback completion sees that committed world and preserves it. -/
theorem static_after_callback (state after : DenoteState)
    (callback response : Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) (succeeded : callback.success = true)
    (continued : (finishLegacyVoidCall state callback meter).1 = .continue after)
    (adversary : Adversary Verity.ContractState Verity.StorageKey) (request : Request)
    (kind : request.kind = .staticcall)
    (executed : executeChecked adversary request after.world = .ok response) :
    response.world = callback.world ∧
      response.returndata = (adversary.respond request callback.world).returndata := by
  have installed := finish_void_success_world state callback meter succeeded
  rw [continued] at installed
  have preserved := checked_static_world adversary request after.world response kind executed
  have bytes := checked_response_current_world adversary request after.world response executed
  exact ⟨preserved.trans installed, installed ▸ bytes⟩

/-- A failed post-call check restores the entire entry world and its exact error bytes. -/
theorem failed_post_call_check_rollback (oracle : DenoteOracle) (fields : List Field)
    (entry : Verity.ContractState) (after : DenoteState) (condition : Expr) (reason : String)
    (failed : evalExpr oracle fields after condition = some 0) :
    Transactions.finishFrame entry (execStmt oracle fields after (.require condition reason)) =
      .ok ⟨false, errorStringBytes reason, entry, false⟩ := by
  rw [execStmt_require_arm, failed]
  exact Transactions.finishFrame_revert entry (errorStringBytes reason)
end Compiler.CompilationModel.SolidityImport.PostCallStaticFrames
