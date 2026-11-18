import Compiler.SolidityImport.IntervalCommand
import Compiler.SolidityImport.IntervalHistoryCertificate
import Compiler.SolidityImport.Differential

/-! Check a source-selected loop with an independent ordered-key table. -/

open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport
open CertifiedInterval IntervalSearch

namespace IntervalHistoryChecks

solidity_import searchLoop from "Contracts/SolidityImportSmoke" entry "LegacyLoopControl.sol"
  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,
          optimizerRuns := some 800, bytecodeHash := "none" }
  interval contract LegacyLoopControl
  function search(uint256,uint256,uint256,uint256)
  loop "LegacyLoopControl.sol" line 27 column 9

private def table (first last needle : Nat) : OrderedSearchWindow where
  first := first
  last := last
  target := 2 * needle + 1
  initialized i := decide (first ≤ i)
  key i := 2 * i
  isInitialized := by intro i _; simp only [decide_eq_true_eq]
  monotone := by intro i j _ h _; omega

private def runCertified (site : Site) (w : OrderedSearchWindow) (pivot : Nat)
    (state : Denote.DenoteState) : Option Nat := do
  if bracket : w.Brackets pivot then
    if retains : w.Retains pivot (site.low state) (site.high state) then
      if fits : w.last < 2 ^ site.bits then
        let entry ← site.checkEntry Differential.oracle w pivot bracket state retains
        let cert := progress_of_checked_history site Differential.oracle w pivot bracket fits
        let .ok (.continue result) := site.execute Differential.oracle cert state entry.down | none
        return Denote.lookupValue result.bindings site.midName
  none

private def runCase (first last needle low high skipMask : Nat) : Option Nat :=
  let site := searchLoop.site
  runCertified site (table first last needle) needle {
    world := Verity.defaultState
    bindings := [(site.lowName, low), (site.highName, high), ("target", needle),
      ("skipMask", skipMask)] }

-- Midpoint exit, immediate continue on a sparse prefix, right and left updates,
-- singleton termination and a target at the first initialized index.
#guard runCase 0 16 7 0 14 0 == some 7
#guard runCase 9 16 12 0 15 511 == some 12
#guard runCase 0 16 0 0 15 0 == some 0
#guard runCase 0 16 15 0 15 0 == some 15
#guard runCase 0 1 0 0 0 0 == some 0
#guard runCase 4 16 4 0 15 15 == some 4

-- A missing bracket, a starting interval that lost the bracket, and an
-- uninitialized singleton whose actual step contradicts the supplied table.
#guard (runCase 0 0 0 0 0 1).isNone
#guard (runCase 0 16 8 9 15 0).isNone
#guard (runCase 0 1 0 0 0 1).isNone

solidity_import storedLoop from "Contracts/SolidityImportSmoke" entry "LegacyStoredIntervalKeys.sol"
  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,
          optimizerRuns := some 800, bytecodeHash := "none" }
  interval contract LegacyStoredIntervalKeys
  function find(uint256,uint256,uint32)
  loop "LegacyStoredIntervalKeys.sol" line 13 column 9

private def checkStored (rows : List (Option Nat)) (physical : List Nat)
    (first last target pivot low high : Nat) : Option Nat := do
  let w ← OrderedSearchWindow.ofRows? (fun i =>
    let cell := rows[i]?.join
    (cell.isSome, cell.getD 0)) first last target
  let site := storedLoop.site
  let world := physical.zipIdx.foldl (init := Verity.defaultState) fun st (value, i) =>
    st.writePhysicalSlot i (Verity.Core.Uint256.ofNat value)
  runCertified site w pivot {
    world, bindings := [(site.lowName, low), (site.highName, high), ("target", target)] }

private def rows : List (Option Nat) := [none, none, none, none, none, some 10, some 20, some 35]
private def packedRows : List Nat := [0, 0, 0, 0, 0, 2^32 + 10, 2^32 + 20, 2^32 + 35]

#guard checkStored rows packedRows 5 7 25 6 0 7 == some 6
#guard checkStored rows packedRows 5 7 11 5 0 7 == some 5
#guard (checkStored rows [0, 0, 0, 0, 0, 0, 0, 0] 5 7 25 6 0 7).isNone

-- Validate finite storage snapshots independently of the emitted iteration.
#guard (OrderedSearchWindow.ofRows? (fun i => (decide (2 ≤ i), i * 3)) 2 6 10).isSome
#guard (OrderedSearchWindow.ofRows? (fun i => (decide (i ≠ 3), i * 3)) 0 6 10).isNone
#guard (OrderedSearchWindow.ofRows? (fun i => (true, if i == 4 then 0 else i)) 0 6 2).isNone

end IntervalHistoryChecks
