import Verity.Core

/-! Exact child logs coexist with legacy typed events in one ordered journal.
External success must preserve the prior journal and supply complete new logs. -/
namespace Compiler.CompilationModel.EventLogs

/-- Append a complete opcode log, optionally retaining the old typed-word view. -/
def append (world : Verity.ContractState) (entry : Verity.EncodedLog)
    (name : String := "") (words : List Verity.Core.Uint256 := []) : Verity.ContractState :=
  { world with events := world.events ++
      [{ name, args := words, indexedArgs := entry.topics, rawLog := some entry }] }

/-- A callee cannot rewrite earlier logs or leave new logs without an emitter/payload.
The four-topic bound belongs to the opcode, not to an ABI event declaration. -/
def validExtension (before after : List Verity.Event) : Bool :=
  decide (after.take before.length = before) &&
    (after.drop before.length).all fun event =>
      match event.rawLog with
      | some entry => entry.topics.length ≤ 4
      | none => false

end Compiler.CompilationModel.EventLogs
