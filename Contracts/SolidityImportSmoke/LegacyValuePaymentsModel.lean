import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.PaymentCallMocks

namespace SolidityImportSmoke.LegacyValuePaymentsModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyValuePayments.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none", sourceGas := true }
  contract LegacyValuePayments
  function pay(uint256,uint256,uint256,address,«address payable»,bool)
  function cursor(«address payable»)
/-- Payments checked against original bytecode, with explicit foreign programs. -/
def model : CompilationModel := imported.model
end SolidityImportSmoke.LegacyValuePaymentsModel

def main (args : List String) : IO UInt32 :=
  Compiler.CompilationModel.SolidityImport.SequenceRunner.run
    SolidityImportSmoke.LegacyValuePaymentsModel.model
    Compiler.CompilationModel.SolidityImport.Differential.oracle args
    (configure := Compiler.CompilationModel.SolidityImport.PaymentCallMocks.configure)
