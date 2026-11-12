import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.RawCallMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyCalldataExecutionModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyCalldataExecution.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyCalldataExecution
  function run(address,uint256,bytes,Operation,uint256)
  function forward(address,uint256,bytes,Operation,uint256)
/-- Imported raw-call fixture, included in the smoke build. -/
def model : CompilationModel := imported.model
/-- Independent Keccak oracle for executable replay. -/
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyCalldataExecutionModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyCalldataExecutionModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyCalldataExecutionModel.model
        SolidityImportSmoke.LegacyCalldataExecutionModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.RawCallMocks.configure)
