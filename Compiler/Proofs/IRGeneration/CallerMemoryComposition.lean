import Compiler.Proofs.IRGeneration.MemorySliceBridge
import Verity.Core.Model.MemoryObservation

/-! Two-run caller observations after explicit physical-memory writes.
These lemmas connect byte agreement to the existing proof-IR reader and hash.
They do not analyze residual masks, infer aliases, or change importer admission. -/

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.PhysicalMemory

/-- Equal physical bytes give equal nonwrapping proof-IR hash inputs. -/
theorem ir_memory_slice_eq_of_read_byte_eq (left right : Verity.ContractState)
    (leftCoherent : Coherent left) (rightCoherent : Coherent right) (offset size : Nat)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (same : ∀ query, offset ≤ query → query < offset + size →
      left.physicalByte query = right.physicalByte query) :
    irMemorySliceBytesBE (fun address => (left.memory address).val) offset size =
      irMemorySliceBytesBE (fun address => (right.memory address).val) offset size := by
  rw [ir_memory_slice_bytes_eq_physical _ leftCoherent _ _ bounded,
    ir_memory_slice_bytes_eq_physical _ rightCoherent _ _ bounded]
  exact Memory.slice_bytes_eq_of_read_byte_eq _ _ _ _ same

/-- Byte agreement transports through the existing concrete memory hash. -/
theorem memory_slice_hash_eq_of_read_byte_eq (left right : Verity.ContractState)
    (leftCoherent : Coherent left) (rightCoherent : Coherent right) (offset size : Nat)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (same : ∀ query, offset ≤ query → query < offset + size →
      left.physicalByte query = right.physicalByte query) :
    abstractKeccakMemorySlice (fun address => (left.memory address).val) offset size =
      abstractKeccakMemorySlice (fun address => (right.memory address).val) offset size := by
  unfold abstractKeccakMemorySlice
  rw [ir_memory_slice_eq_of_read_byte_eq left right leftCoherent rightCoherent offset size
    bounded same]

/-- A common overwrite sequence makes a later hash insensitive to overwritten byte differences. -/
theorem memory_writes_hash_eq_of_eq_outside (left right : Verity.ContractState)
    (leftCoherent : Coherent left) (rightCoherent : Coherent right)
    (writes : List (Nat × Verity.Core.Uint256)) (offset size : Nat)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (same : ∀ query, offset ≤ query → query < offset + size →
      (∀ write ∈ writes, query < write.1 ∨ write.1 + 32 ≤ query) →
      left.physicalByte query = right.physicalByte query) :
    abstractKeccakMemorySlice (fun address =>
      ((writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
        left).memory address).val) offset size =
    abstractKeccakMemorySlice (fun address =>
      ((writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
        right).memory address).val) offset size := by
  exact memory_slice_hash_eq_of_read_byte_eq _ _ (memory_writes_coherent _ leftCoherent writes)
    (memory_writes_coherent _ rightCoherent writes) offset size bounded fun query lower upper =>
      memory_writes_byte_eq_of_eq_outside left right writes query (same query lower upper)

/-- Cover every residual byte in the later hash input before observing that input. -/
theorem memory_writes_hash_eq_of_residual_covered (left right : Verity.ContractState)
    (leftCoherent : Coherent left) (rightCoherent : Coherent right)
    (writes : List (Nat × Verity.Core.Uint256)) (residual : Nat → Prop) (offset size : Nat)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (same : ∀ query, ¬ residual query → left.physicalByte query = right.physicalByte query)
    (covered : ∀ query, offset ≤ query → query < offset + size → residual query →
      ∃ write ∈ writes, write.1 ≤ query ∧ query < write.1 + 32) :
    abstractKeccakMemorySlice (fun address =>
      ((writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
        left).memory address).val) offset size =
    abstractKeccakMemorySlice (fun address =>
      ((writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
        right).memory address).val) offset size := by
  apply memory_slice_hash_eq_of_read_byte_eq _ _ (memory_writes_coherent _ leftCoherent writes)
    (memory_writes_coherent _ rightCoherent writes) offset size bounded
  intro query lower upper
  exact memory_writes_byte_eq_of_residual_covered left right writes residual query
    (same query) (covered query lower upper)

end Compiler.Proofs.IRGeneration
