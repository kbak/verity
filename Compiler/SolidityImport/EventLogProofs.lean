import Verity.Core.Model.EventLogs
import Verity.Core.Model.RawCallProofs
import Compiler.SolidityImport.ValueTransactions

/-! Exact log-journal laws, independent of a particular ABI declaration or callee.
These are model properties, not Solidity/compiler correspondence theorems. -/
namespace Compiler.CompilationModel.SolidityImport.EventLogProofs
open EventLogs ByteExternalCall Transactions ValueTransactions

/-- Appending a log preserves its exact emitter, topics and payload. -/
theorem append_journal (world : Verity.ContractState) (entry : Verity.EncodedLog) :
    (EventLogs.append world entry).events = world.events ++
      [{ name := "", args := [], indexedArgs := entry.topics, rawLog := some entry }] := by
  rfl

/-- Consecutive emissions preserve program order, including repeated equal entries. -/
theorem append_order (world : Verity.ContractState) (first second : Verity.EncodedLog) :
    (EventLogs.append (EventLogs.append world first) second).events = world.events ++
      [{ name := "", args := [], indexedArgs := first.topics, rawLog := some first },
       { name := "", args := [], indexedArgs := second.topics, rawLog := some second }] := by
  simp only [EventLogs.append, List.append_assoc, List.cons_append, List.nil_append]

/-- Emission cannot change balances, nonces, code or persistent account storage. -/
theorem append_accounts (world : Verity.ContractState) (entry : Verity.EncodedLog) :
    (EventLogs.append world entry).accountWorld = world.accountWorld := by
  rfl

/-- The external-log admission check preserves the complete pre-call prefix. -/
theorem validExtension_prefix (before after : List Verity.Event)
    (valid : EventLogs.validExtension before after = true) :
    after.take before.length = before := by
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp valid).1

/-- Successful child commit keeps the child's ordered journal intact. -/
theorem commit_journal (before child : Verity.ContractState) :
    (CallWorld.commitCalleeWorld before child).events = child.events := by
  rfl

/-- A failed child preserves earlier caller/sibling logs, discarding all child effects. -/
theorem failed_child_journal
    (adversary : Adversary Verity.ContractState Verity.StorageKey) (request : Request)
    (before : Verity.ContractState) (after : Observation Verity.ContractState Verity.StorageKey)
    (executed : RawCalls.execute adversary request before = .ok after)
    (failed : after.success = false) : after.world.events = before.events := by
  exact congrArg Verity.ContractState.events (RawCalls.execute_failure_world
    adversary request before after executed failed)

/-- A later outer REVERT restores the full entry journal, even after successful children. -/
theorem outer_revert_journal (before : Verity.ContractState) (bytes : List UInt8) :
    (finishFrame before (.revertWithData bytes)).map (fun result => result.world.events) =
      .ok before.events := by
  rfl

/-- Transaction failure restores the reserved pre-transfer journal as well as funds. -/
theorem failed_transaction_journal (prepared : Prepared) (result : FrameResult)
    (failed : result.success = false) :
    (settle prepared result).world.events = prepared.rollbackWorld.events := by
  simp only [settle, failed, Bool.false_eq_true, ↓reduceIte]

end Compiler.CompilationModel.SolidityImport.EventLogProofs
