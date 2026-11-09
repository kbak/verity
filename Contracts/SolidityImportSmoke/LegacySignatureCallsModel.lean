import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.SignatureMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacySignatureCallsModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacySignatureCalls.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacySignatureCalls
  function recover(bytes32,uint256,bytes32,bytes32)
  function loop(bytes32,uint256,bytes32,bytes32,uint256)
  function abstractWord(address,bytes32,bytes)
  function twice(bytes32,uint256,bytes32,bytes32)
  function inspect(bytes32,uint256,bytes32,bytes32)
  function word(address,bytes32,bytes)
  function scratch(address,bytes32,bytes)
  function check(address,bytes32,bytes)
  function checked(address,bytes32,bytes)
  function gated(bool,address,bytes32,bytes)
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacySignatureCallsModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacySignatureCallsModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacySignatureCallsModel.model
        SolidityImportSmoke.LegacySignatureCallsModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.SignatureMocks.configure)
