import Compiler.SolidityImport.PostCallStaticFrames
import Compiler.SolidityImport.StorageFrames

/-! Scalar continuation writes consume the successful callback's current world.
These are model laws conditional on a supplied child observation, not a proof of
frontend correspondence, callee behavior or general reentrancy safety. -/
namespace Compiler.CompilationModel.SolidityImport.PostCallStorageFrames
open Denote ByteExternalCall PostCallStaticFrames

/-- An actual scalar statement writes into the callback world, never its entry snapshot. -/
theorem write_after_callback (oracle : DenoteOracle) (fields : List Field)
    (state after : DenoteState) (callback : Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) (succeeded : callback.success = true)
    (continued : (finishLegacyVoidCall state callback meter).1 = .continue after)
    (name : String) (value : Expr) (slots : List Nat) (word : Nat)
    (resolved : findFieldWriteSlots fields name = some slots)
    (evaluated : evalExpr oracle fields after value = some word) :
    execStmt oracle fields after (.setStorage name value) =
      .continue { after with
        world := writeUintFieldSlots fields name callback.world slots word } := by
  have installed := finish_void_success_world state callback meter succeeded
  rw [continued] at installed
  rw [execStmt_setStorage_arm, resolved, evaluated]
  simp only [installed]

/-- Packed writes merge with the current callback word, including reentrant neighbor changes. -/
theorem packed_write_after_callback (oracle : DenoteOracle) (fields : List Field)
    (state after : DenoteState) (callback : Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) (succeeded : callback.success = true)
    (continued : (finishLegacyVoidCall state callback meter).1 = .continue after)
    (name : String) (value : Expr) (slots : List Nat) (word slot : Nat)
    (resolved : findFieldWriteSlots fields name = some slots)
    (evaluated : evalExpr oracle fields after value = some word)
    (field : Field) (bits : PackedBits)
    (found : findFieldWithResolvedSlot fields name = some (field, slot))
    (packed : field.packedBits = some bits) (persistent : field.isTransient = false) :
    execStmt oracle fields after (.setStorage name value) = .continue
      { after with
        world := callback.world.modifyPhysicalSlots (slots.map wordNormalize)
          (fun current => packedWordWrite current.val word bits) } := by
  rw [write_after_callback oracle fields state after callback meter succeeded continued
    name value slots word resolved evaluated]
  simp only [writeUintFieldSlots, found, packed, persistent, Bool.false_eq_true, ↓reduceIte]

/-- Other parent slots retain the callback's changes after a successful scalar write. -/
theorem write_after_callback_storage_frame (oracle : DenoteOracle) (fields : List Field)
    (state after written : DenoteState)
    (callback : Observation Verity.ContractState Verity.StorageKey)
    (meter : Option SourceGas.State) (succeeded : callback.success = true)
    (continued : (finishLegacyVoidCall state callback meter).1 = .continue after)
    (name : String) (value : Expr) (slots : List Nat) (slot : Nat)
    (resolved : findFieldWriteSlots fields name = some slots)
    (outside : (slots.map wordNormalize).contains slot = false)
    (executed : execStmt oracle fields after (.setStorage name value) = .continue written) :
    written.world.storage slot = callback.world.storage slot := by
  have installed := finish_void_success_world state callback meter succeeded
  rw [continued] at installed
  exact (execStmt_setStorage_storage_frame oracle fields after written name value slots slot
    resolved outside executed).trans (congrArg (fun world => world.storage slot) installed)
end Compiler.CompilationModel.SolidityImport.PostCallStorageFrames
