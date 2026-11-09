import Compiler.SolidityImport.Import

namespace SolidityImportSmoke.FixedBytesCustomError

solidity_import imported from "Contracts/SolidityImportSmoke" entry "FixedBytesCustomError.sol"
  using
    { solc := "0.8.34+commit.80d5c536",
      evmVersion := "osaka", viaIR := true,
      optimizerRuns := some 200, bytecodeHash := "ipfs" }
  contract FixedBytesCustomError
  function exercise(uint256, uint256)

end SolidityImportSmoke.FixedBytesCustomError
