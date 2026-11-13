import Verity.Core.Model.MemoryComposition

/-! Two-run byte observations after a common sequence of physical word writes.
The relation is pointwise byte equality, compatible with existing resource frames.
These statements neither compare memory sizes nor analyze caller control flow. -/

namespace Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.PhysicalMemory

/-- Identical word writes erase a byte difference inside their footprint. -/
theorem Memory.read_byte_write_word_eq_of_eq_outside (left right : Memory)
    (offset query : Nat) (word : Word)
    (same : query < offset ∨ offset + 32 ≤ query → left.readByte query = right.readByte query) :
    (left.writeWord offset word).readByte query =
      (right.writeWord offset word).readByte query := by
  by_cases inside : offset ≤ query ∧ query < offset + 32
  · let index : Fin 32 := ⟨query - offset, by omega⟩
    have address : offset + index.val = query := by dsimp only [index]; omega
    rw [← address, Memory.readByte_writeWord_at, Memory.readByte_writeWord_at]
  · have outside : query < offset ∨ offset + 32 ≤ query := by omega
    rw [Memory.readByte_writeWord_outside _ _ _ _ outside,
      Memory.readByte_writeWord_outside _ _ _ _ outside]
    exact same outside

/-- A common write sequence needs prior byte agreement only outside every write. -/
theorem memory_writes_byte_eq_of_eq_outside (left right : Verity.ContractState)
    (writes : List (Nat × Verity.Core.Uint256)) (query : Nat)
    (same : (∀ write ∈ writes, query < write.1 ∨ write.1 + 32 ≤ query) →
      left.physicalByte query = right.physicalByte query) :
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      left).physicalByte query =
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      right).physicalByte query := by
  induction writes generalizing left right with
  | nil => exact same (by intro write member; cases member)
  | cons write writes ih =>
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      intro outside
      apply Memory.read_byte_write_word_eq_of_eq_outside
      intro headOutside
      apply same
      intro item member
      rcases List.mem_cons.mp member with rfl | member
      · exact headOutside
      · exact outside item member

/-- Equal physical bytes give equal exact slices, without alignment or size equality. -/
theorem Memory.slice_bytes_eq_of_read_byte_eq (left right : Memory) (offset size : Nat)
    (same : ∀ query, offset ≤ query → query < offset + size →
      left.readByte query = right.readByte query) :
    left.sliceBytes offset size = right.sliceBytes offset size := by
  apply ByteArray.ext
  simp only [Memory.sliceBytes, Memory.slice, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro index member
  have inside : index < size := List.mem_range.mp member
  exact congrArg (fun byte : Byte => UInt8.ofNat byte.val)
    (same (offset + index) (by omega) (by omega))

/-- Compose byte overwrites with an exact caller slice observation. -/
theorem memory_writes_slice_eq_of_eq_outside (left right : Verity.ContractState)
    (writes : List (Nat × Verity.Core.Uint256)) (offset size : Nat)
    (same : ∀ query, offset ≤ query → query < offset + size →
      (∀ write ∈ writes, query < write.1 ∨ write.1 + 32 ≤ query) →
      left.physicalByte query = right.physicalByte query) :
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      left).byteMemory.sliceBytes offset size =
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      right).byteMemory.sliceBytes offset size := by
  exact Memory.slice_bytes_eq_of_read_byte_eq _ _ _ _ fun query lower upper =>
    memory_writes_byte_eq_of_eq_outside left right writes query (same query lower upper)

/-- Coherent word reads agree when all differences in their window have been overwritten. -/
theorem memory_writes_word_eq_of_eq_outside (left right : Verity.ContractState)
    (leftCoherent : Coherent left) (rightCoherent : Coherent right)
    (writes : List (Nat × Verity.Core.Uint256)) (offset : Nat)
    (same : ∀ query, offset ≤ query → query < offset + 32 →
      (∀ write ∈ writes, query < write.1 ∨ write.1 + 32 ≤ query) →
      left.physicalByte query = right.physicalByte query) :
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      left).memory offset =
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      right).memory offset := by
  rw [(memory_writes_coherent left leftCoherent writes) offset,
    (memory_writes_coherent right rightCoherent writes) offset]
  apply congrArg wordValue
  funext index
  exact memory_writes_byte_eq_of_eq_outside left right writes (offset + index.val)
    (same _ (by omega) (by have := index.isLt; omega))

/-- An explicit residual-byte set is discharged only where the common writes cover it. -/
theorem memory_writes_byte_eq_of_residual_covered (left right : Verity.ContractState)
    (writes : List (Nat × Verity.Core.Uint256)) (residual : Nat → Prop) (query : Nat)
    (same : ¬ residual query → left.physicalByte query = right.physicalByte query)
    (covered : residual query → ∃ write ∈ writes, write.1 ≤ query ∧ query < write.1 + 32) :
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      left).physicalByte query =
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      right).physicalByte query := by
  apply memory_writes_byte_eq_of_eq_outside
  intro outside
  by_cases dirty : residual query
  · obtain ⟨write, member, lower, upper⟩ := covered dirty
    have disjoint := outside write member
    omega
  · exact same dirty

/-- Covering the residual bytes in a read range makes the final exact slices equal. -/
theorem memory_writes_slice_eq_of_residual_covered (left right : Verity.ContractState)
    (writes : List (Nat × Verity.Core.Uint256)) (residual : Nat → Prop) (offset size : Nat)
    (same : ∀ query, ¬ residual query → left.physicalByte query = right.physicalByte query)
    (covered : ∀ query, offset ≤ query → query < offset + size → residual query →
      ∃ write ∈ writes, write.1 ≤ query ∧ query < write.1 + 32) :
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      left).byteMemory.sliceBytes offset size =
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      right).byteMemory.sliceBytes offset size := by
  exact Memory.slice_bytes_eq_of_read_byte_eq _ _ _ _ fun query lower upper =>
    memory_writes_byte_eq_of_residual_covered left right writes residual query
      (same query) (covered query lower upper)

end Compiler.CompilationModel.DenoteMemory
