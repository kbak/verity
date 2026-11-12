import Compiler.Proofs.IRGeneration.MemorySliceBridge
import Verity.Core.Model.MemoryComposition
import Compiler.Proofs.MappingSlot
import EvmYul.EVM.Proof.Memory

/-! Exact mapping preimages and scratch isolation in the physical-memory model.
These lemmas compose the existing writer and hash reader; they do not classify
imported statements or establish source/importer correspondence. Hash faithfulness
and storage collision assumptions remain at their existing boundaries. -/

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.PhysicalMemory

/-- Two adjacent physical writes expose the first word followed by the second word. -/
theorem write_word_pair_bytes (world : Verity.ContractState) (offset : Nat)
    (first second : Verity.Core.Uint256) :
    (writeWordPair world offset first second).byteMemory.sliceBytes offset 64 =
      irWordToBytesBE first.val ++ irWordToBytesBE second.val := by
  change (writeWordPair world offset first second).byteMemory.sliceBytes offset (32 + 32) = _
  rw [Memory.slice_bytes_append,
    ← ir_word_bytes_coherent _ (write_word_pair_coherent _ _ _ _) offset,
    ← ir_word_bytes_coherent _ (write_word_pair_coherent _ _ _ _) (offset + 32),
    write_word_pair_first, write_word_pair_second]

/-- The proof-IR word encoder agrees with the existing EVM word encoder. -/
theorem ir_word_bytes_eq_evm_word (word : EvmYul.UInt256) :
    irWordToBytesBE word.toNat = word.toByteArray := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [EvmYul.UInt256.toList_data_toByteArray]
  change (List.range 32).map (fun index => UInt8.ofNat (word.toNat / 256 ^ (31 - index) % 256)) = _
  apply List.ext_getElem (by simp only [List.length_map, List.length_range,
    EvmYul.length_toBeBytesFixed])
  intro index inside _
  simp only [List.getElem_map, List.getElem_range, EvmYul.getElem_toBeBytesFixed]

/-- A bounded physical word needs no further normalization in the EVM encoder. -/
theorem bounded_word_bytes_eq_evm_word (word : Verity.Core.Uint256) :
    irWordToBytesBE word.val = (EvmYul.UInt256.ofNat word.val).toByteArray := by
  have normalized : (EvmYul.UInt256.ofNat word.val).toNat = word.val := by
    change word.val % Verity.Core.Uint256.modulus = word.val
    exact Nat.mod_eq_of_lt word.isLt
  simpa only [normalized] using ir_word_bytes_eq_evm_word (EvmYul.UInt256.ofNat word.val)

/-- Physical scratch bytes have the existing mapping preimage's key-then-base order. -/
theorem write_word_pair_mapping_preimage (world : Verity.ContractState) (offset : Nat)
    (key baseSlot : Verity.Core.Uint256) :
    (writeWordPair world offset key baseSlot).byteMemory.sliceBytes offset 64 =
      Compiler.Proofs.abiEncodeMappingSlot baseSlot.val key.val := by
  rw [write_word_pair_bytes, bounded_word_bytes_eq_evm_word, bounded_word_bytes_eq_evm_word]
  rfl

/-- Nonwrapping proof-IR reads see that same ordered mapping preimage. -/
theorem ir_mapping_preimage_after_word_pair (world : Verity.ContractState) (offset : Nat)
    (key baseSlot : Verity.Core.Uint256) (bounded : offset + 64 ≤ Compiler.Constants.evmModulus) :
    irMemorySliceBytesBE (fun address =>
      ((writeWordPair world offset key baseSlot).memory address).val) offset 64 =
      Compiler.Proofs.abiEncodeMappingSlot baseSlot.val key.val := by
  rw [ir_memory_slice_bytes_eq_physical _ (write_word_pair_coherent _ _ _ _) _ _ bounded]
  exact write_word_pair_mapping_preimage _ _ _ _

/-- The existing concrete memory hash consumes exactly the canonical mapping preimage. -/
theorem mapping_hash_after_word_pair (world : Verity.ContractState) (offset : Nat)
    (key baseSlot : Verity.Core.Uint256) (bounded : offset + 64 ≤ Compiler.Constants.evmModulus) :
    abstractKeccakMemorySlice (fun address =>
      ((writeWordPair world offset key baseSlot).memory address).val) offset 64 =
      KeccakEngine.byteArrayToNatBE
        (KeccakEngine.keccak256 (Compiler.Proofs.abiEncodeMappingSlot baseSlot.val key.val)) %
          Compiler.Constants.evmModulus := by
  unfold abstractKeccakMemorySlice
  rw [ir_mapping_preimage_after_word_pair _ _ _ _ bounded]

/-- Disjoint writes preserve the hash of an arbitrary, possibly unaligned byte slice. -/
theorem word_pair_hash_frame (world : Verity.ContractState) (coherent : Coherent world)
    (offset query size : Nat) (first second : Verity.Core.Uint256)
    (outside : query + size ≤ offset ∨ offset + 64 ≤ query)
    (bounded : query + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus) :
    abstractKeccakMemorySlice (fun address =>
      ((writeWordPair world offset first second).memory address).val) query size =
      abstractKeccakMemorySlice (fun address => (world.memory address).val) query size := by
  rw [abstract_keccak_memory_slice_eq_physical _ (write_word_pair_coherent _ _ _ _) _ _ bounded,
    abstract_keccak_memory_slice_eq_physical _ coherent _ _ bounded,
    write_word_pair_slice_frame _ _ _ _ _ _ outside]

/-- Canonical scratch writes preserve both allocator and zero-word observations. -/
theorem scratch_pair_allocator_frame (world : Verity.ContractState) (coherent : Coherent world)
    (key baseSlot : Verity.Core.Uint256) :
    (writeWordPair world 0 key baseSlot).memory 64 = world.memory 64 ∧
      (writeWordPair world 0 key baseSlot).memory 96 = world.memory 96 := by
  exact ⟨write_word_pair_word_frame world coherent 0 64 key baseSlot (Or.inr (by decide)),
    write_word_pair_word_frame world coherent 0 96 key baseSlot (Or.inr (by decide))⟩

/-- Canonical scratch writes preserve any source buffer above the reserved memory region. -/
theorem scratch_pair_buffer_frame (world : Verity.ContractState) (buffer size : Nat)
    (key baseSlot : Verity.Core.Uint256) (high : 128 ≤ buffer) :
    (writeWordPair world 0 key baseSlot).byteMemory.sliceBytes buffer size =
      world.byteMemory.sliceBytes buffer size := by
  exact write_word_pair_slice_frame world 0 buffer size key baseSlot (Or.inr (by omega))

/-- Storage and event projections follow from the complete non-memory frame. -/
theorem scratch_pair_storage_events_frame (world : Verity.ContractState)
    (key baseSlot : Verity.Core.Uint256) :
    (writeWordPair world 0 key baseSlot).storageWords = world.storageWords ∧
      (writeWordPair world 0 key baseSlot).events = world.events := by
  have frame := write_word_pair_frame world 0 key baseSlot
  simpa only [installPhysicalMemory_storage_frame, installPhysicalMemory_events_frame] using
    Prod.mk.inj (congrArg (fun s : Verity.ContractState => (s.storageWords, s.events)) frame)

end Compiler.Proofs.IRGeneration
