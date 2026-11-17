import Verity.Core.Model.Denote
import Compiler.CompilationModel.AbiHelpers
import Compiler.Keccak.Sponge

/-! Exact ordered log observations shared by the bounded and observed adapters.
Legacy typed events need their declaration; opcode logs already carry exact bytes. -/
namespace Compiler.CompilationModel.SolidityImport.EventObservation
open Denote Verity.Core

/-- Scalar ABI cleanup matching the compiler's event-word normalization. -/
private def eventWord (ty : ParamType) (value : Nat) : Except String Nat := do
  match ty with
  | .uint256 | .bytes32 => pure (value % 2^256)
  | .uint8 => pure (value % 2^8)
  | .uint16 => pure (value % 2^16)
  | .uintN bits =>
      unless 0 < bits && bits ≤ 256 && bits % 8 == 0 do throw "invalid event integer width"
      pure (value % 2^bits)
  | .bytesN 4 => pure ((value % 2^256) &&& ((2^32 - 1) * 2^224))
  | .bytesN 1 => pure ((value % 2^256) &&& ((2^8 - 1) * 2^248))
  | .address => pure (value % 2^160)
  | .bool => pure (if value == 0 then 0 else 1)
  | _ => throw "unsupported event observation parameter type"

/-- Encode one journal entry without changing an already observed opcode log.
Typed entries require a unique declaration and preserve source argument order. -/
def encode (account : Address) (definitions : List EventDef)
    (event : Verity.Event) : Except String Verity.EncodedLog := do
  if let some entry := event.rawLog then
    unless entry.topics.length ≤ 4 do throw "logged event has more than four topics"
    return entry
  let [definition] := definitions.filter (·.name == event.name)
    | throw s!"observed event must resolve uniquely: {event.name}"
  unless event.indexedArgs.isEmpty do
    unless event.indexedArgs.length ≤ 4 do throw "logged event has more than four topics"
    return {
      emitter := account
      topics := event.indexedArgs
      data := event.args.flatMap (fun word => wordBytes word.val) }
  unless definition.params.length == event.args.length do throw "event argument count differs"
  let pairs ← (definition.params.zip event.args).mapM fun (parameter, value) => do
    pure (parameter, ← eventWord parameter.ty value.val)
  let indexed := pairs.filter (fun p => p.1.kind == .indexed)
  unless indexed.length ≤ 3 do throw "event has more than three indexed parameters"
  let topic0 := Uint256.ofNat (KeccakEngine.keccak256_str_nat (eventSignature definition))
  let topics := topic0 :: indexed.map (fun p => Uint256.ofNat p.2)
  let data := (pairs.filter (fun p => p.1.kind == .unindexed)).flatMap (fun p => wordBytes p.2)
  return { emitter := account, topics, data }

end Compiler.CompilationModel.SolidityImport.EventObservation
