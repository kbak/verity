import Compiler.Proofs.IRGeneration.MemorySlice
import Verity.Core.Model.MemorySlice

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.PhysicalMemory

/-- Each chunk address lies below the bound on the complete word window. -/
theorem chunk_base_lt (offset count limit index : Nat)
    (bounded : offset + count * 32 ≤ limit) (inside : index < count) :
    offset + index * 32 < limit := by
  omega

/-- Rounding the byte count upward covers even a partial final word. -/
theorem byte_word_count_covers (size : Nat) : size ≤ byteWordCount size * 32 := by
  unfold byteWordCount
  omega

/-- Decode one complete word from the coherent physical view. -/
theorem ir_word_bytes_coherent (world : Verity.ContractState) (coherent : Coherent world)
    (offset : Nat) :
    irWordToBytesBE (world.memory offset).val = world.byteMemory.sliceBytes offset 32 := by
  apply ByteArray.ext
  simp only [irWordToBytesBE, Memory.sliceBytes, Memory.slice, List.map_map, Function.comp_def]
  apply congrArg List.toArray
  apply List.map_congr_left
  intro index member
  have inside : index < 32 := List.mem_range.mp member
  have byte : (world.memory offset).val / 256 ^ (31 - index) % 256 =
      (world.physicalByte (offset + index)).val := by
    rw [coherent offset]
    exact congrArg (fun word : Word => (word ⟨index, inside⟩).val)
      (valueWord_wordValue (world.byteMemory.readWord offset))
  exact congrArg UInt8.ofNat byte

/-- Concatenating coherent word windows retains every physical byte, without alignment. -/
theorem physical_memory_chunks (world : Verity.ContractState) (coherent : Coherent world)
    (offset count : Nat) :
    (List.range count).foldl
      (fun bytes index => bytes ++ irWordToBytesBE (world.memory (offset + index * 32)).val)
      ByteArray.empty = world.byteMemory.sliceBytes offset (count * 32) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, ir_word_bytes_coherent world coherent, Nat.succ_mul, Memory.slice_bytes_append]

/-- Non-wrapping chunk addresses make modular and natural word reads coincide. -/
theorem memory_slice_words_eq_of_bounded (memory : Nat → Nat) (offset size : Nat)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus) :
    memorySliceWords memory offset size =
      (List.range (byteWordCount size)).map (fun index => memory (offset + index * 32)) := by
  unfold memorySliceWords
  apply List.map_congr_left
  intro index member
  have inside := List.mem_range.mp member
  rw [Nat.mod_eq_of_lt (chunk_base_lt offset (byteWordCount size) _ index bounded inside)]

/-- Exact bridge from the actual proof-IR hash reader to the physical byte slice. -/
theorem ir_memory_slice_bytes_eq_physical (world : Verity.ContractState)
    (coherent : Coherent world) (offset size : Nat)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus) :
    irMemorySliceBytesBE (fun address => (world.memory address).val) offset size =
      world.byteMemory.sliceBytes offset size := by
  unfold irMemorySliceBytesBE
  rw [memory_slice_words_eq_of_bounded _ offset size bounded, List.foldl_map]
  rw [physical_memory_chunks world coherent offset (byteWordCount size)]
  exact Memory.slice_bytes_extract _ offset _ size (byte_word_count_covers size)

/-- Equality of hash inputs transports through the existing concrete hash implementation. -/
theorem abstract_keccak_memory_slice_eq_physical (world : Verity.ContractState)
    (coherent : Coherent world) (offset size : Nat)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus) :
    abstractKeccakMemorySlice (fun address => (world.memory address).val) offset size =
      KeccakEngine.byteArrayToNatBE
        (KeccakEngine.keccak256 (world.byteMemory.sliceBytes offset size)) %
          Compiler.Constants.evmModulus := by
  unfold abstractKeccakMemorySlice
  rw [ir_memory_slice_bytes_eq_physical world coherent offset size bounded]

end Compiler.Proofs.IRGeneration
