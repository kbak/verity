import Compiler.SolidityImport.Import

namespace SolidityImportSmoke.LegacyOrderedSignaturesImport
open Compiler.CompilationModel

solidity_import imported from "Contracts/SolidityImportSmoke" entry "LegacyOrderedSignatures.sol"
  using {
    solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false
    optimizerRuns := none, bytecodeHash := "none" }
  contract LegacyOrderedSignatures
  function checkN(address,bytes32,bytes,uint256)
  function checkThreshold(address,bytes32,bytes)

end SolidityImportSmoke.LegacyOrderedSignaturesImport
