import Compiler.SolidityImport.Import
import Compiler.SolidityImport.TypedCallGasFrames
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.GasCallMocks

namespace SolidityImportSmoke.LegacyTypedCallGasModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyTypedCallGas.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none", sourceGas := true }
  contract LegacyTypedCallGas
  function run(address,address,bytes,bytes,bool)
  function settle(address,uint256,uint256,bytes)
/-- Source-site-bound typed calls, including roots with no explicit gasleft(). -/
def model : CompilationModel := imported.model
end SolidityImportSmoke.LegacyTypedCallGasModel

def main (args : List String) : IO UInt32 :=
  Compiler.CompilationModel.SolidityImport.SequenceRunner.run
    SolidityImportSmoke.LegacyTypedCallGasModel.model
    Compiler.CompilationModel.SolidityImport.Differential.oracle args
    (configure := Compiler.CompilationModel.SolidityImport.GasCallMocks.configure)
