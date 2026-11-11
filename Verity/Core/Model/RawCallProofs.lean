import Verity.Core.Model.RawCalls

/-! Frame properties of the functional raw-call boundary; no EVM equivalence claim. -/
namespace Compiler.CompilationModel.RawCalls
open ByteExternalCall Verity.Core

/-- Every failed admitted raw call restores the entire caller world. -/
theorem execute_failure_world (adversary : Adversary Verity.ContractState Verity.StorageKey)
    (request : Request) (before : Verity.ContractState)
    (after : Observation Verity.ContractState Verity.StorageKey)
    (executed : execute adversary request before = .ok after)
    (failed : after.success = false) : after.world = before := by
  simp only [execute, bind, Except.bind, pure, Except.pure] at executed
  repeat' split at executed
  all_goals cases executed
  all_goals simp_all only [Bool.true_eq_false]

/-- Delegate frames execute in the parent's storage context, with inherited sender/value. -/
theorem delegate_context (request : Request) (world : Verity.ContractState)
    (kind : request.kind = .delegatecall) :
    childAddress request world = world.thisAddress ∧
    childSender request world = world.sender ∧ childValue request world = world.msgValue := by
  simp only [childAddress, childSender, childValue, kind]
  exact ⟨rfl, rfl, rfl⟩

/-- The commit projection restores the parent address, sender, value and memories. -/
theorem commit_context (before after : Verity.ContractState) :
    (CallWorld.commitCalleeWorld before after).thisAddress = before.thisAddress ∧
    (CallWorld.commitCalleeWorld before after).sender = before.sender ∧
    (CallWorld.commitCalleeWorld before after).msgValue = before.msgValue ∧
    (CallWorld.commitCalleeWorld before after).memory = before.memory ∧
    (CallWorld.commitCalleeWorld before after).byteMemory = before.byteMemory := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
end Compiler.CompilationModel.RawCalls
