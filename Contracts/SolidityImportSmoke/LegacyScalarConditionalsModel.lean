import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyScalarConditionalsModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyScalarConditionals.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyScalarConditionals
  function choose(bool,uint256,uint256)
  function maximum(uint256,uint256)
  function nested(bool,bool,uint256,uint256,uint256)
  function wrapped(bool,uint8,uint8)
  function promoted(bool,uint8,uint16)
  function booleans(bool,bool,bool)
  function addresses(bool,address,address)
  function fixedBytes(bool,bytes32,bytes32)
  function widenedBytes(bool,bytes32,bytes32)
  function guarded(uint256,uint256)
  function narrowGuarded(uint256,uint8)
  function guardedNested(uint256,uint256,bool)
  function lazy(bool,uint256)
  function negated(bool,uint256)
  function requireChoice(bool,uint256)
  function helperArg(bool,uint256,uint256)
  function skippedCopy(bool,bytes)
/-- Source-derived lazy scalar conditional fixture. -/
def model : CompilationModel := imported.model
/-- Executable keccak oracle for exact calldata payloads. -/
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyScalarConditionalsModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyScalarConditionalsModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyScalarConditionalsModel.model
        SolidityImportSmoke.LegacyScalarConditionalsModel.oracle args
