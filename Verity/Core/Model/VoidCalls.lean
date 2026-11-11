import Verity.Core.Model.PhysicalMemory
import Verity.Core.Model.RawCalls
import Verity.Core.Model.LegacyVoidCalls

/-! Physical ABI-v1 input construction for the closed void-call transport.
Memory reads observe preceding stores, as in the original compiler. -/
namespace Compiler.CompilationModel.VoidCalls
open Compiler.Yul.LegacyVoidCalls Verity.Core

/-- Encode all arguments at the current free pointer without advancing it.
The caller validates descriptor arity before entering this total encoder. -/
def encode (world : Verity.ContractState) (selector : Nat) (layout : List Argument)
    (values : List Nat) (inputByte : Nat → DenoteMemory.Byte) :
    Verity.ContractState × Nat := Id.run do
  let ptr := (world.memory 64).val
  let write := fun (w : Verity.ContractState) p n => w.writePhysicalMemoryValue p (Uint256.ofNat n)
  let mut world := write world ptr (selector * 2^224)
  let mut tail := ptr + 4 + 32 * layout.length
  let mut operand := 1
  for (kind, index) in layout.zipIdx do
    if kind == .word then
      world := write world (ptr + 4 + 32 * index) values[operand]!
    operand := operand + (if kind == .calldataBytes then 2 else 1)
  operand := 1
  for (kind, index) in layout.zipIdx do
    let head := ptr + 4 + 32 * index
    let data := values[operand]!
    if kind != .word then
      world := write world head (tail - (ptr + 4))
      let size := if kind == .calldataBytes then values[operand+1]!
        else (world.memory ((data + 2^256 - 32) % 2^256)).val
      world := write world tail size
      let size := if kind == .memoryBytes then (world.memory ((data + 2^256 - 32) % 2^256)).val
        else size
      let rounded := ((size + 31) / 32) * 32
      if kind == .calldataBytes then
        world := world.copyPhysicalMemory inputByte (tail + 32) data size
        world := write world (tail + 32 + size) 0
      else
        world := (List.range ((size + 31) / 32)).foldl (fun w i =>
          write w (tail + 32 + i * 32) (w.memory (data + i * 32)).val) world
        if size % 32 != 0 then
          world := write world (tail + rounded)
            (Nat.land (world.memory (tail + rounded)).val (2^256 - 2^(8 * (rounded - size))))
      tail := tail + 32 + rounded
    operand := operand + (if kind == .calldataBytes then 2 else 1)
  return (world, tail - ptr)

end Compiler.CompilationModel.VoidCalls
