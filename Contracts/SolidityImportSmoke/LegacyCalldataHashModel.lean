import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.SignatureMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyCalldataHashModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyCalldataHash.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyCalldataHash
  function digest(bytes,address,Mode,bytes32,uint256)
  function copy(bytes,uint256,uint256)
  function overlap(bytes)
  function narrow(bytes,uint8,address,bool)
  function cast(uint256)
  function castSmall(uint8)
  function echo(Mode)
  function integer(Mode)
  function length(bytes)
/-- Imported calldata copying and enum fixture, also built by the CI smoke target. -/
def model : CompilationModel := imported.model
/-- Concrete hash oracle used by the executable comparison driver. -/
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyCalldataHashModel

/-- Compile the fixture to Yul or replay an explicit sequence of call frames. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyCalldataHashModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyCalldataHashModel.model
        SolidityImportSmoke.LegacyCalldataHashModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.SignatureMocks.configure)
