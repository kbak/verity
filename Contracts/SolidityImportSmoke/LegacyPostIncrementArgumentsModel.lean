import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyPostIncrementArgumentsModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyPostIncrementArguments.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyPostIncrementArguments
  function set(uint256)
  function last(uint256,bool,bool)
  function first(uint256,bool)
  function middle(uint256,bool)
  function discard(uint256)
  function pair(uint256)
  function nested(uint256)
  function forward(bytes)
  function digest(bytes,uint256)
  function copy(bytes)
  function localCounter(uint256,uint256)
  function narrow(uint8,uint256)
  function aliases(uint256)
/-- Source-derived independent post-increment argument fixture. -/
def model : CompilationModel := imported.model
/-- Executable keccak oracle for exact calldata payloads. -/
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyPostIncrementArgumentsModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyPostIncrementArgumentsModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyPostIncrementArgumentsModel.model
        SolidityImportSmoke.LegacyPostIncrementArgumentsModel.oracle args
