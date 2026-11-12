import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.PaymentCallMocks

namespace SolidityImportSmoke.LegacyNativeValueModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyValuePayments.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyValuePayments
  function cursor(«address payable»)
/-- Gas-free native call fixture for generated-bytecode regression checks. -/
def model : CompilationModel := imported.model
end SolidityImportSmoke.LegacyNativeValueModel

def main (args : List String) : IO UInt32 :=
  Compiler.CompilationModel.SolidityImport.SequenceRunner.run
    SolidityImportSmoke.LegacyNativeValueModel.model
    Compiler.CompilationModel.SolidityImport.Differential.oracle args
    (configure := Compiler.CompilationModel.SolidityImport.PaymentCallMocks.configure)
