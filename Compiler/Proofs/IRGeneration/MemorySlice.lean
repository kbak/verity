import Compiler.Constants
import Compiler.Keccak.Sponge

namespace Compiler.Proofs.IRGeneration

/-- Number of words needed to cover a byte slice. -/
def byteWordCount (size : Nat) : Nat :=
  (size + 31) / 32

/-- Word reads wrap the byte offset mod `2^256`, matching EVM `UInt256`
address arithmetic (compiled code computes scratch offsets with the wrapping
`add` builtin, so reads must land on the same keys as the stores). -/
def memorySliceWords (memory : Nat → Nat) (offset size : Nat) : List Nat :=
  (List.range (byteWordCount size)).map
    (fun i => memory ((offset + i * 32) % Compiler.Constants.evmModulus))

/-- Big-endian 32-byte encoding of a proof-IR memory word. -/
def irWordToBytesBE (word : Nat) : ByteArray :=
  ⟨((List.range 32).map
    (fun index => UInt8.ofNat ((word / (256 ^ (31 - index))) % 256))).toArray⟩

/-- Byte slice read by `keccak256(offset, size)` from the proof IR's word view.
Successive cells start at `offset + 32 * index`; the final cell is truncated.
The base need not be aligned. `MemorySliceBridge` relates this reader to actual
physical bytes under explicit coherence and non-wrapping bounds. -/
def irMemorySliceBytesBE (memory : Nat → Nat) (offset size : Nat) : ByteArray :=
  let bytes := (memorySliceWords memory offset size).foldl
    (fun acc word => acc ++ irWordToBytesBE word)
    ByteArray.empty
  bytes.extract 0 size

/-- Proof-side model of `keccak256(offset, size)` over linear memory, using
the in-tree Ethereum Keccak implementation on the exact requested byte slice. -/
def abstractKeccakMemorySlice (memory : Nat → Nat) (offset size : Nat) : Nat :=
  KeccakEngine.byteArrayToNatBE
      (KeccakEngine.keccak256 (irMemorySliceBytesBE memory offset size)) %
    Compiler.Constants.evmModulus

end Compiler.Proofs.IRGeneration
