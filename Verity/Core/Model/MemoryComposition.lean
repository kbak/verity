import Verity.Core.Model.MemorySlice

/-! Composition lemmas for the existing physical-memory writer. Addresses here
are natural numbers; callers connecting to modular EVM readers must supply their
nonwrapping bounds. The non-memory frame allows memory size to change. -/

namespace Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.PhysicalMemory

/-- Perform two adjacent physical word writes in source order. -/
def writeWordPair (world : Verity.ContractState) (offset : Nat)
    (first second : Verity.Core.Uint256) : Verity.ContractState :=
  (world.writePhysicalMemoryValue offset first).writePhysicalMemoryValue (offset + 32) second

/-- Physical write sequences preserve a disjoint byte slice. -/
theorem memory_writes_slice_frame (world : Verity.ContractState)
    (writes : List (Nat × Verity.Core.Uint256)) (offset size : Nat)
    (outside : ∀ write ∈ writes, offset + size ≤ write.1 ∨ write.1 + 32 ≤ offset) :
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      world).byteMemory.sliceBytes offset size = world.byteMemory.sliceBytes offset size := by
  apply ByteArray.ext
  simp only [Memory.sliceBytes, Memory.slice, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro index member
  have inside : index < size := List.mem_range.mp member
  apply congrArg (fun byte : Byte => UInt8.ofNat byte.val)
  apply memory_writes_byte_frame
  intro write member
  have disjoint := outside write member
  omega

/-- Coherent word observations survive a disjoint sequence of physical writes. -/
theorem memory_writes_word_frame (world : Verity.ContractState) (coherent : Coherent world)
    (writes : List (Nat × Verity.Core.Uint256)) (query : Nat)
    (outside : ∀ write ∈ writes, query + 32 ≤ write.1 ∨ write.1 + 32 ≤ query) :
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      world).memory query = world.memory query := by
  induction writes generalizing world with
  | nil => rfl
  | cons write writes ih =>
      have tailOutside : ∀ item ∈ writes, query + 32 ≤ item.1 ∨ item.1 + 32 ≤ query := by
        intro item member
        exact outside item (List.mem_cons_of_mem write member)
      rw [List.foldl_cons, ih _ (writePhysicalMemoryValue_coherent _ _ _) tailOutside]
      exact writePhysicalMemoryWord_outside world write.1 (valueWord write.2) query coherent
        (outside write (List.mem_cons_self))

/-- The final physical write establishes the complete coherent word view. -/
theorem write_word_pair_coherent (world : Verity.ContractState) (offset : Nat)
    (first second : Verity.Core.Uint256) : Coherent (writeWordPair world offset first second) := by
  exact writePhysicalMemoryValue_coherent _ _ _

/-- The second word does not overwrite any byte of the first word. -/
theorem write_word_pair_first (world : Verity.ContractState) (offset : Nat)
    (first second : Verity.Core.Uint256) :
    (writeWordPair world offset first second).memory offset = first := by
  change ((world.writePhysicalMemoryValue offset first).writePhysicalMemoryWord
    (offset + 32) (valueWord second)).memory offset = first
  rw [writePhysicalMemoryWord_outside _ (offset + 32) (valueWord second) offset
    (writePhysicalMemoryValue_coherent _ _ _) (Or.inl (Nat.le_refl _))]
  exact writePhysicalMemoryValue_at _ _ _

/-- The final word write is observed exactly at its start. -/
theorem write_word_pair_second (world : Verity.ContractState) (offset : Nat)
    (first second : Verity.Core.Uint256) :
    (writeWordPair world offset first second).memory (offset + 32) = second := by
  exact writePhysicalMemoryValue_at _ _ _

/-- Two adjacent writes preserve every non-memory state component. -/
theorem write_word_pair_frame (world : Verity.ContractState) (offset : Nat)
    (first second : Verity.Core.Uint256) :
    (writeWordPair world offset first second).installPhysicalMemory Memory.empty =
      world.installPhysicalMemory Memory.empty := by
  exact memory_writes_frame world [(offset, first), (offset + 32, second)]

/-- A word disjoint from the complete pair retains its coherent observation. -/
theorem write_word_pair_word_frame (world : Verity.ContractState) (coherent : Coherent world)
    (offset query : Nat) (first second : Verity.Core.Uint256)
    (outside : query + 32 ≤ offset ∨ offset + 64 ≤ query) :
    (writeWordPair world offset first second).memory query = world.memory query := by
  apply memory_writes_word_frame world coherent [(offset, first), (offset + 32, second)]
  intro write member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp only <;> omega

/-- A byte slice disjoint from the complete pair is unchanged, including unaligned slices. -/
theorem write_word_pair_slice_frame (world : Verity.ContractState)
    (offset query size : Nat) (first second : Verity.Core.Uint256)
    (outside : query + size ≤ offset ∨ offset + 64 ≤ query) :
    (writeWordPair world offset first second).byteMemory.sliceBytes query size =
      world.byteMemory.sliceBytes query size := by
  apply memory_writes_slice_frame world [(offset, first), (offset + 32, second)]
  intro write member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp only <;> omega

end Compiler.CompilationModel.DenoteMemory
