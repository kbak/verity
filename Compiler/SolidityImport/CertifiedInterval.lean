import Compiler.SolidityImport.IntervalSite
import Compiler.SolidityImport.IntervalSearchProofs
import Verity.Core.Model.Denote

namespace Compiler.CompilationModel.SolidityImport.CertifiedInterval
open Denote LoopExecution

/-- Lower endpoint in the selected lexical frame. -/
def Site.low (site : Site) (s : DenoteState) : Nat := lookupValue s.bindings site.lowName

/-- Upper endpoint in the selected lexical frame. -/
def Site.high (site : Site) (s : DenoteState) : Nat := lookupValue s.bindings site.highName

/-- Inclusive interval size, zero when the bounds cross. -/
def Site.width (site : Site) (s : DenoteState) : Nat := site.high s + 1 - site.low s

/-- Check captured scalar reads before Denote's default-zero lookup can observe an
incomplete frame. The two declared unsigned endpoints must also fit their source width. -/
def Site.framePresent (site : Site) (s : DenoteState) : Bool :=
  let fits (name : String) := (lookupBinding? s.bindings name).any (· < 2 ^ site.bits)
  fits site.lowName && fits site.highName &&
    site.inputs.all (fun name => (lookupBinding? s.bindings name).isSome)

/-- Execute the actual lowered iteration. A bare denotation fallback is an adapter error.
Explicit source halts, side effects before a transfer, and the source break flag are retained. -/
def Site.step (site : Site) (oracle : DenoteOracle) (s : DenoteState) :
    Step DenoteState (Except String StmtOutcome) := Id.run do
  unless site.framePresent s do return .halt (.error "missing or invalid interval frame binding")
  let body := Stmt.letVar site.doneName (.literal 0) :: site.body
  return match execStmtList oracle site.fields s body with
  | .continue t =>
    match lookupBinding? t.bindings site.doneName with
    | some 0 => .next t
    | some 1 => .halt (.ok (.continue t))
    | _ => .halt (.error "invalid interval transfer flag")
  | .revert => .halt (.error "unsupported interval step evaluation")
  | outcome => .halt (.ok outcome)

/-- A progress certificate talks about this exact site, oracle and domain. Valid states
must evaluate successfully, retain a nonempty interval and halve it on every continuation. -/
structure Progress (site : Site) (oracle : DenoteOracle) (Valid : DenoteState → Prop) : Prop where
  nonempty : ∀ s, Valid s → 0 < site.width s
  bounded : ∀ s, Valid s → site.width s ≤ 2 ^ site.bits
  supported : ∀ s, Valid s → ∀ msg, site.step oracle s ≠ .halt (.error msg)
  progress : ∀ s t, Valid s → site.step oracle s = .next t →
    Valid t ∧ site.width t ≤ site.width s / 2

/-- Execute only from a certified loop-head state. The width-derived budget includes the
last source exit. The finite-exit proof rules out exhaustion. -/
def Site.execute (site : Site) (oracle : DenoteOracle) {Valid : DenoteState → Prop}
    (cert : Progress site oracle Valid) (s : DenoteState) (initial : Valid s) :
    Except String StmtOutcome :=
  let run := LoopExecution.execute (site.step oracle) (site.bits + 1) s
  run.get (by
    obtain ⟨result, observed⟩ := IntervalSearch.exists_execute_eq_some_of_interval_progress
      (site.step oracle) Valid site.width cert.nonempty cert.progress site.bits s initial
      (cert.bounded s initial)
    exact Option.isSome_iff_exists.mpr ⟨result, observed⟩)

end Compiler.CompilationModel.SolidityImport.CertifiedInterval
