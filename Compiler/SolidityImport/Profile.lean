/-!
Compiler settings for a Solidity import.

A profile is an ordinary value, so it can be named, reused and `#print`ed:

```lean
def build : Profile :=
  { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
```

The settings are passed to solc and are part of the import digest. They should
match the settings the audited bytecode is built with.
-/
namespace Compiler.CompilationModel.SolidityImport

structure Profile where
  /-- Exact solc release. The importer accepts only its pinned releases
      (0.7.6, 0.8.10, 0.8.26 and 0.8.34 with their exact commit suffixes).
      The legacy release admits only its documented scalar subset. -/
  solc : String := "0.8.34+commit.80d5c536"
  evmVersion : String
  viaIR : Bool
  /-- Optimizer runs; `none` disables the optimizer. -/
  optimizerRuns : Option Nat
  /-- solc `metadata.bytecodeHash`, e.g. `"none"` or `"ipfs"`. -/
  bytecodeHash : String
  /-- Verify gas against original bytecode evidence. Gas reads cannot be recompiled. -/
  sourceGas : Bool := false
  /-- Deployment evidence JSON, relative to the Solidity project root. The immutable
      words are checked against freshly compiled runtime references and code bytes. -/
  deployedImmutables : Option String := none
  deriving Repr, BEq, Inhabited

end Compiler.CompilationModel.SolidityImport
