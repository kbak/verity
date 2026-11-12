import Compiler.SolidityImport.Import
import Compiler.SolidityImport.StaticCallGasFrames
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Contracts.SolidityImportSmoke.StaticGasMocks

namespace SolidityImportSmoke.LegacyStaticCallGasModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyStaticCallGas.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none", sourceGas := true }
  contract LegacyStaticCallGas
  function recover(bytes32,uint256,bytes32,bytes32)
  function repeated(bytes32,uint256,bytes32,bytes32)
  function boundary(bytes32,uint256,bytes32,bytes32)
  function word(address,bytes32,bytes)
  function checked(address,bytes32,bytes)
  function predicate(address,uint256)
  function gated(bool,address,uint256)
/-- Original-bytecode recovery and ABI-v1 static calls with explicit evidence. -/
def model : CompilationModel := imported.model
end SolidityImportSmoke.LegacyStaticCallGasModel

def main (args : List String) : IO UInt32 :=
  Compiler.CompilationModel.SolidityImport.SequenceRunner.run
    SolidityImportSmoke.LegacyStaticCallGasModel.model
    Compiler.CompilationModel.SolidityImport.Differential.oracle args
    (configure := Contracts.SolidityImportSmoke.StaticGasMocks.configure)
