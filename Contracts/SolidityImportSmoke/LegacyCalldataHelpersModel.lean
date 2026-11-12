import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyCalldataHelpersModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyCalldataHelpers.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyCalldataHelpers
  function forward(bytes)
  function copy(bytes)
  function pair(bytes,bytes)
  function siblings(bytes)
  function live(bytes)
  function aliasPointer(bytes)
  function dirty(bytes)
  function mixed(bytes,bytes)
  function copyThenForward(bytes)
  function skipped(bytes,bool)
  function through(bytes)
  function skipCopy(bytes)
  function skipForward(bytes)
/-- Source-derived forwarding and implicit memory-copy fixture. -/
def model : CompilationModel := imported.model
/-- Executable keccak oracle for exact calldata payloads. -/
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyCalldataHelpersModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyCalldataHelpersModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyCalldataHelpersModel.model
        SolidityImportSmoke.LegacyCalldataHelpersModel.oracle args
