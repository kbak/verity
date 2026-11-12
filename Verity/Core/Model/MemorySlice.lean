import Verity.Core.Model.ByteMemoryInverse
import Init.Data.ByteArray.Lemmas
import Init.Data.List.Nat.Range

namespace Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.PhysicalMemory

/-- Byte-array view of an exact, zero-extended physical memory slice. -/
def Memory.sliceBytes (memory : Memory) (offset size : Nat) : ByteArray :=
  ⟨((memory.slice offset size).map (fun byte => UInt8.ofNat byte.val)).toArray⟩

/-- A chunk may start at any address; coherence exposes each requested physical byte. -/
theorem physical_byte_word_offset (world : Verity.ContractState)
    (coherent : Coherent world) (offset index : Nat) :
    valueWord (world.memory (offset + index / 32 * 32))
      ⟨index % 32, Nat.mod_lt _ (by decide)⟩ = world.physicalByte (offset + index) := by
  rw [coherent (offset + index / 32 * 32), valueWord_wordValue]
  change world.byteMemory.readByte (offset + index / 32 * 32 + index % 32) =
    world.byteMemory.readByte (offset + index)
  congr 1
  omega

/-- Arithmetic byte extraction equals the corresponding physical byte value. -/
theorem physical_byte_word_offset_value (world : Verity.ContractState)
    (coherent : Coherent world) (offset index : Nat) :
    (world.memory (offset + index / 32 * 32)).val / 256 ^ (31 - index % 32) % 256 =
      (world.physicalByte (offset + index)).val := by
  exact congrArg Fin.val (physical_byte_word_offset world coherent offset index)

/-- A non-wrapping address makes modular chunk reads agree with physical bytes. -/
theorem physical_byte_word_offset_mod (world : Verity.ContractState)
    (coherent : Coherent world) (offset index : Nat)
    (bounded : offset + index < Verity.Core.Uint256.modulus) :
    (world.memory ((offset + index / 32 * 32) % Verity.Core.Uint256.modulus)).val /
        256 ^ (31 - index % 32) % 256 = (world.physicalByte (offset + index)).val := by
  have baseBound : offset + index / 32 * 32 < Verity.Core.Uint256.modulus := by omega
  rw [Nat.mod_eq_of_lt baseBound]
  exact physical_byte_word_offset_value world coherent offset index

/-- Adjacent physical byte slices concatenate exactly, including empty slices. -/
theorem Memory.slice_bytes_append (memory : Memory) (offset left right : Nat) :
    memory.sliceBytes offset (left + right) =
      memory.sliceBytes offset left ++ memory.sliceBytes (offset + left) right := by
  apply ByteArray.ext
  simp only [sliceBytes, Memory.slice, List.range_add, List.map_append, List.map_map,
    List.append_toArray, ByteArray.data_append, Function.comp_def, Nat.add_assoc]

/-- Truncating a physical byte slice retains exactly the requested prefix. -/
theorem Memory.slice_bytes_extract (memory : Memory) (offset total size : Nat)
    (bounded : size ≤ total) :
    (memory.sliceBytes offset total).extract 0 size = memory.sliceBytes offset size := by
  apply ByteArray.ext
  simp only [sliceBytes, Memory.slice, ByteArray.data_extract, List.extract_toArray,
    List.extract_eq_take_drop, Nat.sub_zero, List.drop_zero, ← List.map_take,
    List.take_range, Nat.min_eq_left bounded]

/-- An arbitrary sequence of overlapping writes preserves a coherent word view. -/
theorem memory_writes_coherent (world : Verity.ContractState) (coherent : Coherent world)
    (writes : List (Nat × Verity.Core.Uint256)) :
    Coherent (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      world) := by
  induction writes generalizing world with
  | nil => exact coherent
  | cons write writes ih =>
      exact ih _ (writePhysicalMemoryValue_coherent _ _ _)

/-- A byte outside every write footprint survives the complete sequence. -/
theorem memory_writes_byte_frame (world : Verity.ContractState)
    (writes : List (Nat × Verity.Core.Uint256)) (query : Nat)
    (outside : ∀ write ∈ writes, query < write.1 ∨ write.1 + 32 ≤ query) :
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      world).physicalByte query = world.physicalByte query := by
  induction writes generalizing world with
  | nil => rfl
  | cons write writes ih =>
      have tailOutside : ∀ item ∈ writes, query < item.1 ∨ item.1 + 32 ≤ query := by
        intro item member
        exact outside item (List.mem_cons_of_mem write member)
      rw [List.foldl_cons, ih _ tailOutside]
      exact writePhysicalMemoryValue_byte_outside world write.1 write.2 query
        (outside write (List.mem_cons_self))

/-- A sequence of physical writes preserves every non-memory state component. -/
theorem memory_writes_frame (world : Verity.ContractState)
    (writes : List (Nat × Verity.Core.Uint256)) :
    (writes.foldl (fun state write => state.writePhysicalMemoryValue write.1 write.2)
      world).installPhysicalMemory Memory.empty = world.installPhysicalMemory Memory.empty := by
  induction writes generalizing world with
  | nil => rfl
  | cons write writes ih =>
      rw [List.foldl_cons, ih]
      rfl

/-- Exact chunked byte reader used by the differential hash oracle. -/
def wordMemorySliceBytes (memory : Nat → Verity.Core.Uint256) (offset size : Nat) : ByteArray :=
  let bytes := (List.range size).toArray.map fun index =>
    UInt8.ofNat ((memory (offset + index / 32 * 32)).val / 2^(8*(31-index % 32)) % 256)
  ByteArray.mk bytes

/-- The concrete oracle byte reader equals the physical slice at any base address. -/
theorem word_memory_slice_bytes_eq_physical (world : Verity.ContractState)
    (coherent : Coherent world) (offset size : Nat) :
    wordMemorySliceBytes world.memory offset size = world.byteMemory.sliceBytes offset size := by
  apply ByteArray.ext
  simp only [wordMemorySliceBytes, Memory.sliceBytes, Memory.slice, ← List.map_toArray,
    List.map_map, Function.comp_def]
  congr 1
  funext index
  rw [Nat.pow_mul]
  change UInt8.ofNat ((world.memory (offset + index / 32 * 32)).val /
    256 ^ (31 - index % 32) % 256) = _
  rw [physical_byte_word_offset_value world coherent offset index]
  rfl

end Compiler.CompilationModel.DenoteMemory
