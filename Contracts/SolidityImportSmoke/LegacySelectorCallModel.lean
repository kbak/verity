import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.CallResponderMocks
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace SolidityImportSmoke.LegacySelectorCall
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacySelectorCall.sol"
  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,
          optimizerRuns := some 800, bytecodeHash := "none" }
  contract LegacySelectorCall
  function checked(address,address,uint256)
  function inspect(address,address,uint256)

/-- Emit Yul for bytecode replay and run the same model against recording child accounts. -/
def replay (selectors : List Nat) (yul input output : String) : IO Unit := do
  let compiled ← IO.ofExcept (compile imported.model selectors)
  IO.FS.writeFile yul (Compiler.Yul.render (Compiler.emitYul compiled))
  let status ← SolidityImport.SequenceRunner.run imported.model SolidityImport.Differential.oracle
    [input, output] (configure := SolidityImport.CallResponderMocks.configure)
  unless status == 0 do throw (IO.userError "selector call replay failed")

end SolidityImportSmoke.LegacySelectorCall
