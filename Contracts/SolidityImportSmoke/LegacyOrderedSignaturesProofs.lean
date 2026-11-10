import Contracts.SolidityImportSmoke.LegacyOrderedSignaturesImport
import Compiler.SolidityImport.OrderedEntryPoint
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! Kernel certificates for actual imported ordered-signature entrypoints.
The proof is about Denote execution; differential campaigns cover source/compiled correspondence.
-/
namespace SolidityImportSmoke.LegacyOrderedSignaturesProofs
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport
open Denote AuthorizationFrames OrderedAuthorization LegacyOrderedSignaturesImport


/-- The complete entrypoint imported from Solidity, without hand-translated statements. -/
def top (entry : Fin 2) : List Stmt :=
  ((imported.model.functions[entry.val]?).map (·.body)).getD []

/-- Signature loop extracted from the full imported body. -/
def loop (entry : Fin 2) : List Stmt :=
  match (top entry)[if entry == 0 then 28 else 31]? with
  | Option.some (Compiler.CompilationModel.Stmt.forEach _ _ body) => body
  | _ => []

/-- Temporary names are checked against the entire imported body by `body_eq`. -/
def names : OrderedGuard.Names := fun i =>
  match i.val with
  | 0 => "current"
  | 1 => "previous"
  | 2 => "_verity_slice_tmp_49"
  | 3 => "_verity_slice_tmp_50"
  | 4 => "_verity_slice_tmp_48"
  | 5 => "_verity_slice_tmp_51"
  | 6 => "_verity_slice_tmp_52"
  | _ => "_verity_slice_tmp_53"

/-- A literal false require is a rejecting suffix for both guards. -/
def failure (message : String) : List Stmt := [.require (.literal 0) message]

/-- Exact signature resolution and final ordering guard. -/
def guard (entry : Fin 2) : Guard := {
  names, field := "members", member := "__solidity_value", sentinel := 1,
  resolution := (loop entry).take 8, failure := failure "member",
  indexVar := "i", frameKey := "_authorization_frame" }

/-- Reassembly retains every original statement, including ABI decoding and the final return. -/
def program (entry : Fin 2) : Program := {
  guard := guard entry,
  countName := if entry == 0 then "_verity_slice_tmp_9" else "required",
  countExpr := if entry == 0 then .calldataload (.literal 100) else .storage "threshold",
  start := (top entry).take 18,
  middle := ((top entry).drop 19).take (if entry == 0 then 7 else 10),
  setup := ((top entry).drop (if entry == 0 then 27 else 30)).take 1,
  tail := if entry == 0 then [] else ((top entry).drop 32).take 1,
  returns := if entry == 0 then [.literal 1] else [.localVar "_verity_slice_tmp_54"] }

/-- Generated locals cannot alias each other. -/
theorem names_fresh : Function.Injective names := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [names] at *

/-- Failure cannot be confused with a successful continuation. -/
theorem failure_rejects (o : DenoteOracle) (message : String) (state after : DenoteState) :
    execStmtList o imported.model.fields state (failure message) ≠ .continue after := by
  simp [failure, exec_singleton, execStmt, evalExpr, wordNormalize]

/-- Every structural frame obligation is decided on the actual imported statements. -/
theorem certificate (entry : Fin 2) (o : DenoteOracle) :
    (program entry).Certificate o imported.model.fields := by
  fin_cases entry
  all_goals
    constructor
    · exact ⟨names_fresh, by decide, by decide, failure_rejects o "member", by decide⟩
    all_goals decide

/-- Kernel equality prevents the certificate from omitting or replacing imported code. -/
theorem body_eq (entry : Fin 2) : (program entry).body = top entry := by
  fin_cases entry <;> rfl

/-- Each successful entry resolves exactly the counted distinct registered valid addresses. -/
theorem authorized (entry : Fin 2) (o : DenoteOracle) (state final : DenoteState)
    (executed : execStmtList o imported.model.fields state (top entry) = .stop final) :
    Nonempty (EntryEvidence o imported.model.fields (program entry) state) := by
  rw [← body_eq] at executed
  exact entry_authorized o imported.model.fields (program entry) (certificate entry o)
    state final executed

/-- The wrapper additionally requires a positive threshold from the initial storage snapshot. -/
theorem threshold_authorized (o : DenoteOracle) (state final : DenoteState)
    (executed : execStmtList o imported.model.fields state (top 1) = .stop final) :
    ∃ evidence : EntryEvidence o imported.model.fields (program 1) state,
      storageValue o imported.model.fields state.world "threshold" = some evidence.count ∧
      0 < evidence.count := by
  obtain ⟨evidence⟩ := authorized 1 o state final executed
  refine ⟨evidence, evidence_stored_count o imported.model.fields (program 1) state evidence
    "threshold" rfl, ?_⟩
  exact evidence_positive o imported.model.fields (program 1) state evidence
    "_verity_slice_tmp_9" (failure "threshold") ((program 1).middle.drop 2) rfl
    (failure_rejects o "threshold")

end SolidityImportSmoke.LegacyOrderedSignaturesProofs
