import Compiler.SolidityImport.Import
import Compiler.SolidityImport.PostCallMemoryFrames
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.VoidCallMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyPostCallMemoryLoopsModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyPostCallMemoryLoops.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyPostCallMemoryLoops
  function configure(uint256)
  function readCallback()
  function runCalldata(address,uint256,bytes,Operation,bytes,uint256)
  function notify(address,bytes,bytes,Operation,uint256)
  function mixed(address,bytes,bytes,Operation,uint256)
  function aliasBuffers(address,bytes,bytes,Operation,uint256,uint256)
  function headAlias(address,bytes,bytes,Operation,uint256)
  function lengthAlias(address,bytes,bytes,Operation,uint256)
/-- Imported void callback fixture, included in the smoke build. -/
def model : CompilationModel := imported.model
/-- Independent Keccak oracle for executable replay. -/
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end SolidityImportSmoke.LegacyPostCallMemoryLoopsModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        SolidityImportSmoke.LegacyPostCallMemoryLoopsModel.model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        SolidityImportSmoke.LegacyPostCallMemoryLoopsModel.model
        SolidityImportSmoke.LegacyPostCallMemoryLoopsModel.oracle args
        (configure := Compiler.CompilationModel.SolidityImport.VoidCallMocks.configure)
