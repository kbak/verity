import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.SignatureMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyStaticAbiHashModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyStaticAbiHash.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyStaticAbiHash
  function digest(bytes32,uint256,address)
  function scalars(uint256,address,bool,bytes32)
  function raw(uint8,address,bool,bytes32)
  function literals()
  function empty()
  function domain()
  function viaHelper(bytes32)
  function inspect(bytes,bytes32,uint256)
  function mixed(bytes32,uint256)
  function loop(bytes32,uint256)
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyStaticAbiHashModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyStaticAbiHashModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyStaticAbiHashModel.model
        SolidityImportSmoke.LegacyStaticAbiHashModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.SignatureMocks.configure)
