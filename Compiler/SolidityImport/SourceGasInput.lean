import Verity.Core.Model.SourceGas
import Lean.Data.Json

/-! Strict JSON boundary for original-bytecode gas evidence. Provenance is
validated by the source-execution adapter; this parser never supplies defaults. -/
namespace Compiler.CompilationModel.SolidityImport.SourceGasInput
open Lean SourceGas ByteExternalCall

private def nat (j : Json) (key : String) : Except String Nat := do
  let value ← (← j.getObjVal? key).getNat?
  unless value < 2^256 do throw "source gas field exceeds EVM word"
  return value

private def boolean (j : Json) (key : String) : Except String Bool := do
  (← j.getObjVal? key).getBool?

private def bytes (j : Json) (key : String) : Except String Bytes := do
  (← (← j.getObjVal? key).getArr?).toList.mapM fun value => do
    let n ← value.getNat?
    unless n < 256 do throw "source gas byte exceeds uint8"
    return UInt8.ofNat n

private def call (j : Json) : Except String SourceGas.Call := do
  let kind ← match ← (← j.getObjVal? "kind").getStr? with
    | "call" => pure Kind.call
    | "delegatecall" => pure Kind.delegatecall
    | "staticcall" => pure Kind.staticcall
    | _ => throw "source gas requires CALL, DELEGATECALL or STATICCALL"
  let c ← j.getObjVal? "context"
  let delegationWarm : Option Bool ← match ← c.getObjVal? "delegationWarm" with
    | .null => pure none
    | value => pure (some (← value.getBool?))
  let context : CallGas.Context := {
    memoryWords := ← nat c "memoryWords"
    inputOffset := ← nat c "inputOffset"
    inputSize := ← nat c "inputSize"
    outputOffset := ← nat c "outputOffset"
    outputSize := ← nat c "outputSize"
    targetWarm := ← boolean c "targetWarm"
    targetDead := ← boolean c "targetDead"
    transfersValue := ← boolean c "transfersValue"
    delegationWarm }
  let request : Request := {
    kind
    caller := ← nat j "caller"
    target := ← nat j "target"
    value := ← nat j "value"
    gas := ← nat j "gas"
    calldata := ← bytes j "calldata" }
  unless request.caller < 2^160 && request.target < 2^160 do
    throw "source gas address exceeds uint160"
  return {
    context, request
    allowance := ← nat j "allowance"
    exceptional := ← boolean j "exceptional"
    gasLeft := ← nat j "gasLeft"
    success := ← boolean j "success"
    returndata := ← bytes j "returndata" }

/-- Decode one explicitly supplied meter; missing entries and fields are errors. -/
def parse (j : Json) : Except String State := do
  let remaining ← nat j "remaining"
  let events ← (← (← j.getObjVal? "events").getArr?).toList.mapM fun event => do
    let cost ← nat event "cost"
    match ← (← event.getObjVal? "type").getStr? with
    | "read" =>
        let site ← (← event.getObjVal? "site").getStr?
        unless !site.isEmpty do throw "empty source gas site"
        pure (Event.read site cost)
    | "call" => return Event.call cost (← call event)
    | "end" => pure (Event.endFrame cost)
    | _ => throw "unknown source gas event"
  return { remaining, events }

end Compiler.CompilationModel.SolidityImport.SourceGasInput
