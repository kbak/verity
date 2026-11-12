import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.StaticBoolMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyStaticInstallationModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyStaticInstallation.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyStaticInstallation
  function seedResponse(address,uint256,uint256,uint256,bytes32)
  function install(address)
  function installAndFail(address)
  function readCandidate()
  function readWord()
  function storeWord(uint256)
  function probe(address,bytes32)
  function probeMany(address,uint256,bytes32,address,bool,bytes32)
  function probeEmpty(address)
  function probePair(address,address)
  function advertises(bytes32)
/-- Imported scalar staticcall and fixed-slot installation fixture, included in the smoke build. -/
def model : CompilationModel := imported.model
/-- Independent Keccak oracle for executable replay. -/
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyStaticInstallationModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyStaticInstallationModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyStaticInstallationModel.model
        SolidityImportSmoke.LegacyStaticInstallationModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.StaticBoolMocks.configure)
