import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.ExceptionalHalt
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyMemoryArraysModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyMemoryArrays.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyMemoryArrays
  function allocate(uint256)
  function echo(«address[]»)
  function read(«address[]»,uint256)
  function replace(«address[]»,uint256,address)
  function sumPrefix(«address[]»,uint256)
  function sumOffset(«address[]»)
  function sumExpanded(«address[]»)
  function fill(«address[]»)
  function enumerate()
/-- Source-derived ABI-v1 allocation, mutation, return, and traversal fixture. -/
def model : CompilationModel := imported.model
/-- Existing executable keccak oracle for physical mapping slots. -/
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyMemoryArraysModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyMemoryArraysModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyMemoryArraysModel.model
        SolidityImportSmoke.LegacyMemoryArraysModel.oracle args
