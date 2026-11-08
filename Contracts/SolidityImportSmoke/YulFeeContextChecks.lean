import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Access
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.YulFeeContextChecks
open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport Verity.Core

solidity_import fees from "Contracts/SolidityImportSmoke" entry "YulFeeContext.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract FeeContext
  function readFees()

/-- Distinct nonzero fee inputs catch swapped, dropped, or constant context reads. -/
def check : IO Unit := do
  let oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
  for (base, price) in [(0, 0), (13, 17), (2 ^ 256 - 1, 1), (0, 2 ^ 256 - 1)] do
    let world := { Verity.defaultState with
      baseFee := Uint256.ofNat base, gasPrice := Uint256.ofNat price }
    let result := runFunction oracle fees.model "readFees" world []
    unless result == some [base, price, (3 * base + price) % (2 ^ 256)] do
      throw (IO.userError s!"Yul fee context mismatch for {base}, {price}: {result}")
  let compiled ← IO.ofExcept (Compiler.CompilationModel.compile fees.model [0x12345678] .osaka)
  let yul := Compiler.Yul.render (Compiler.emitYul compiled)
  unless (yul.splitOn "basefee()").length > 1 && (yul.splitOn "gasprice()").length > 1 do
    throw (IO.userError "compiled fee context lost an environmental opcode")
  IO.println "Yul fee context: four nonzero/boundary cases and compilation passed."

end SolidityImportSmoke.YulFeeContextChecks

/-- Execute the Yul context regression checks. -/
def main : IO Unit := SolidityImportSmoke.YulFeeContextChecks.check
