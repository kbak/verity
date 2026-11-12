import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Contracts.SolidityImportSmoke.StaticGasMocks
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacyStaticWordModel
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyStaticWord.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyStaticWord
  function word(address,address)
  function selfWord(address)
  function twice(address,address,address)
  function inspect(address,address)
  function decoded(address,address)
  function inspectPair(address,address,address)
  function atLeast(address,address,uint256)
end SolidityImportSmoke.LegacyStaticWordModel

/-- Compile the gas-free model, or replay with an explicit static child environment. -/
def main (args : List String) : IO UInt32 := do
  let model := SolidityImportSmoke.LegacyStaticWordModel.imported.model
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile model selectors .osaka)
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run model
        Compiler.CompilationModel.SolidityImport.Differential.oracle args
        (configure := fun input =>
          if (input.getObjVal? "staticGasChildren").isOk then
            Contracts.SolidityImportSmoke.StaticGasMocks.configure input
          else Compiler.CompilationModel.SolidityImport.SignatureMocks.configure input)
