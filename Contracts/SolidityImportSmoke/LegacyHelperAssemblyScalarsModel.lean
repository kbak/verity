import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyHelperAssemblyScalarsModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyHelperAssemblyScalars.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyHelperAssemblyScalars
  function set(uint256)
  function direct(address,Mode,uint8,bool)
  function nested(address,Mode)
  function pair(address,Mode)
  function payableAddress(«address payable»)
  function repeated(address,address)
  function checkedEnum(Mode)
  function record(address,Mode,bool)
  function digest(address,Mode,bool)
/-- Source-derived assembly reads through immutable scalar helper parameters. -/
def model : CompilationModel := imported.model
/-- Executable keccak oracle for exact calldata payloads. -/
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyHelperAssemblyScalarsModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyHelperAssemblyScalarsModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyHelperAssemblyScalarsModel.model
        SolidityImportSmoke.LegacyHelperAssemblyScalarsModel.oracle args
