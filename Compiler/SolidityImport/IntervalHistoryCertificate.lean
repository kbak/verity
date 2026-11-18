import Compiler.SolidityImport.CertifiedInterval
import Compiler.SolidityImport.OrderedSearchPath

namespace Compiler.CompilationModel.SolidityImport.CertifiedInterval
open Denote IntervalSearch OrderedSearchWindow LoopExecution

/-- Only a completed denotation, including an explicit source halt, is an admissible exit. -/
def isSourceExit : Except String StmtOutcome → Bool
  | .ok _ => true
  | .error _ => false

/-- The initial bounds retain a bracket, and every continuing edge of this particular
source iteration agrees with the independently supplied ordered history. -/
def Site.CheckedEntry (site : Site) (oracle : DenoteOracle) (w : OrderedSearchWindow)
    (pivot : Nat) (s : DenoteState) : Prop :=
  w.Retains pivot (site.low s) (site.high s) ∧
    CheckedPath w (site.step oracle) site.low site.high isSourceExit s

/-- A checked path ending in a source outcome cannot treat an adapter error as a halt. -/
theorem step_ne_error_of_checked_entry {site : Site} {oracle : DenoteOracle}
    {w : OrderedSearchWindow} {pivot : Nat} {s : DenoteState}
    (entry : site.CheckedEntry oracle w pivot s) (msg : String) :
    site.step oracle s ≠ .halt (.error msg) := by
  intro bad
  cases entry.2 with
  | exit h source =>
    rw [bad] at h
    cases h
    cases source
  | next h _ _ =>
    rw [bad] at h
    contradiction

/-- Build the source-bound progress proof from the sorted table and its checked path. -/
theorem progress_of_checked_history (site : Site) (oracle : DenoteOracle)
    (w : OrderedSearchWindow) (pivot : Nat) (bracket : w.Brackets pivot)
    (fits : w.last < 2 ^ site.bits) : Progress site oracle (site.CheckedEntry oracle w pivot) := by
  constructor
  · intro s entry
    obtain ⟨left, right, _⟩ := entry.1
    unfold Site.width
    omega
  · intro s entry
    obtain ⟨_, _, last⟩ := entry.1
    unfold Site.width
    omega
  · intro s entry msg
    exact step_ne_error_of_checked_entry entry msg
  · intro s t entry next
    obtain ⟨moves, tail⟩ := moves_and_tail_of_next entry.2 next
    obtain ⟨retained, shrink⟩ := w.progress_of_moves bracket entry.1 moves
    exact ⟨⟨retained, tail⟩, shrink⟩

/-- Verify a concrete starting frame against the supplied ordered history. The certificate
is indexed by the actual site, frame and oracle; unsupported steps cannot produce one. -/
def Site.checkEntry (site : Site) (oracle : DenoteOracle) (w : OrderedSearchWindow)
    (pivot : Nat) (bracket : w.Brackets pivot) (s : DenoteState)
    (retains : w.Retains pivot (site.low s) (site.high s)) :
    Option (PLift (site.CheckedEntry oracle w pivot s)) :=
  (w.checkPath (site.step oracle) site.low site.high isSourceExit pivot bracket s retains).map
    fun path => ⟨⟨retains, path.down⟩⟩

end Compiler.CompilationModel.SolidityImport.CertifiedInterval
