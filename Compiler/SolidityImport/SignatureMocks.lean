import Compiler.SolidityImport.StaticOracleMocks

/-! Test-only external environment. Recovery rows are computed independently by
the Python secp256k1 library before either EVM route runs. Only exact requests
in that finite domain are admitted. Unknown requests are instrumentation errors,
never a zero signer. Contract behavior is the calldata-hashing program. -/
namespace Compiler.CompilationModel.SolidityImport.SignatureMocks
open Denote DenoteByteExternalCalls ByteExternalCall

private def decimal (j : Lean.Json) : Except String Nat := do
  let s ← j.getStr?
  let some n := s.toNat? | throw "signature oracle expects decimal words"
  unless n < 2^256 do throw "signature oracle word exceeds uint256"
  return n

/-- Configure exact precompile requests and the separately modeled validator
fallback. No response is learned from a source or compiled EVM observation. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let base ← StaticOracleMocks.configure input
  let some contracts := base.adversary | throw "contract oracle missing"
  let config ← input.getObjVal? "byteCallEnvironment"
  let rows ← (← (← config.getObjVal? "recoveries").getArr?).toList.mapM fun row => do
    let words ← (← (← row.getObjVal? "args").getArr?).toList.mapM decimal
    unless words.length == 4 do throw "recovery requires four words"
    let output ← (← (← row.getObjVal? "output").getArr?).toList.mapM decimal
    unless output.length ≤ 1 && output.all (· < 2^160) do
      throw "recovery response must be empty or an address word"
    return (words.flatMap wordBytes, output.flatMap wordBytes)
  unless (rows.map Prod.fst).eraseDups.length == rows.length do
    throw "duplicate recovery oracle request"
  let recovery := staticAdversary fun request _ =>
    (true, (rows.find? (·.1 == request.calldata)).map Prod.snd |>.getD [], [])
  return { base with adversary := some {
    respond := fun request world => if request.target == 1 then
      recovery.respond request world else contracts.respond request world
    accepts := fun request world => if request.target == 1 then
      request.kind == .staticcall && request.value == 0 &&
        rows.any (·.1 == request.calldata)
      else contracts.accepts request world
    valid := by
      intro request world
      split
      · exact recovery.valid request world
      · exact contracts.valid request world } }

end Compiler.CompilationModel.SolidityImport.SignatureMocks
