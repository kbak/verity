import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.GasCallMocks

namespace SolidityImportSmoke.LegacyGasObservationsModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyGasObservations.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none", sourceGas := true }
  contract LegacyGasObservations
  function observe()
  function ordered(bool)
  function guarded(uint256)
  function run(address,uint256,uint256,bytes,bool,bool,bool)
  function assemblyGas(address)
  function forward(address,uint256,bool)
  function twice(address)
  function forwardData(address,bytes,Operation,uint256,bool)
/-- Source-only model: gas-sensitive recompilation is deliberately unavailable. -/
def model : CompilationModel := imported.model
end SolidityImportSmoke.LegacyGasObservationsModel

def main (args : List String) : IO UInt32 :=
  Compiler.CompilationModel.SolidityImport.SequenceRunner.run
    SolidityImportSmoke.LegacyGasObservationsModel.model
    Compiler.CompilationModel.SolidityImport.Differential.oracle args
    (configure := Compiler.CompilationModel.SolidityImport.GasCallMocks.configure)
