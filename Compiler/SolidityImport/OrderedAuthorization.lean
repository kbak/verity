import Compiler.SolidityImport.OrderedGuard

namespace Compiler.CompilationModel.SolidityImport.OrderedAuthorization
open Denote

/-- Signers observed after actual continuing loop iterations, with full execution evidence. -/
inductive Trace (indexVar previous : String) (runBody : DenoteState → StmtOutcome) :
    Nat → DenoteState → List Nat → DenoteState → Prop
  | nil (index : Nat) (state : DenoteState) : Trace indexVar previous runBody index state [] state
  | cons {index : Nat} {state next final : DenoteState} {rest : List Nat}
      (step : runBody { state with
        bindings := bindValue state.bindings indexVar (wordNormalize index) } = .continue next)
      (tail : Trace indexVar previous runBody (index + 1) next rest final) :
      Trace indexVar previous runBody index state (lookupValue next.bindings previous :: rest) final

/-- A strictly ordered prefix of registered, nonsentinel signers above a lower bound. -/
def OrderedMembers (member : Nat → Prop) (sentinel lower : Nat) (used : List Nat) : Prop :=
  (∀ signer ∈ used, lower < signer ∧ member signer ∧ signer ≠ sentinel) ∧
    used.Pairwise (· < ·)

/-- The common guard extends a certified prefix by exactly one distinct signer. -/
theorem ordered_cons (member : Nat → Prop) (sentinel lower current : Nat) (rest : List Nat)
    (step : lower < current ∧ member current ∧ current ≠ sentinel)
    (tail : OrderedMembers member sentinel current rest) :
    OrderedMembers member sentinel lower (current :: rest) := by
  refine ⟨?_, List.pairwise_cons.mpr ⟨fun signer h => (tail.1 signer h).1, tail.2⟩⟩
  intro signer h
  rcases List.mem_cons.mp h with same | later
  · subst signer; exact step
  · have h := tail.1 signer later
    exact ⟨Nat.lt_trans step.1 h.1, h.2⟩

/-- Arbitrary-count authorization for the actual executor, preserving its full state invariant.
The step premise is discharged by the imported guard and structural frame certificates. -/
theorem loop_authorized (indexVar previous : String) (runBody : DenoteState → StmtOutcome)
    (member : Nat → Prop) (sentinel : Nat) (invariant : DenoteState → Prop)
    (step : ∀ index state next, invariant state →
      runBody { state with bindings := bindValue state.bindings indexVar (wordNormalize index) } =
        .continue next → invariant next ∧
      lookupValue state.bindings previous < lookupValue next.bindings previous ∧
      member (lookupValue next.bindings previous) ∧ lookupValue next.bindings previous ≠ sentinel)
    (remaining index : Nat) (state final : DenoteState) (initial : invariant state)
    (executed : execForEachLoop indexVar runBody state index remaining = .continue final) :
    ∃ used, Trace indexVar previous runBody index state used final ∧ used.length = remaining ∧
      OrderedMembers member sentinel (lookupValue state.bindings previous) used := by
  induction remaining generalizing index state with
  | zero =>
      simp only [execForEachLoop, StmtOutcome.continue.injEq] at executed
      subst final
      exact ⟨[], Trace.nil _ _, rfl, by simp [OrderedMembers]⟩
  | succ remaining ih =>
      cases bodyStep : runBody
          { state with bindings := bindValue state.bindings indexVar (wordNormalize index) } with
      | «continue» next =>
          have rest :
              execForEachLoop indexVar runBody next (index + 1) remaining = .continue final :=
            by simpa only [execForEachLoop, bodyStep] using executed
          have certified := step index state next initial bodyStep
          obtain ⟨used, trace, length, ordered⟩ := ih (index + 1) next certified.1 rest
          exact ⟨_ :: used, Trace.cons bodyStep trace, by simp [length],
            ordered_cons member sentinel _ _ used certified.2 ordered⟩
      | stop next => simp [execForEachLoop, bodyStep] at executed
      | «return» value next => simp [execForEachLoop, bodyStep] at executed
      | revert => simp [execForEachLoop, bodyStep] at executed
      | revertWithData bytes => simp [execForEachLoop, bodyStep] at executed

/-- Strict ordering implies distinctness, without assuming distinct signatures. -/
theorem ordered_nodup (member : Nat → Prop) (sentinel lower : Nat) (used : List Nat)
    (ordered : OrderedMembers member sentinel lower used) : used.Nodup :=
  ordered.2.imp (fun {a b} h equal => by subst b; exact Nat.lt_irrefl a h)

/-- Starting at zero rules out zero-address authorization as well as the sentinel. -/
theorem ordered_authorized (member : Nat → Prop) (sentinel : Nat) (used : List Nat)
    (ordered : OrderedMembers member sentinel 0 used) :
    used.Nodup ∧ ∀ signer ∈ used, member signer ∧ signer ≠ 0 ∧ signer ≠ sentinel := by
  refine ⟨ordered_nodup member sentinel 0 used ordered, ?_⟩
  intro signer h
  have row := ordered.1 signer h
  exact ⟨row.2.1, Nat.ne_of_gt row.1, row.2.2⟩

end Compiler.CompilationModel.SolidityImport.OrderedAuthorization

namespace Compiler.CompilationModel.SolidityImport.MemberRead
open Denote

/-- Membership is read through the same field layout and packing as the imported expression. -/
def read (o : DenoteOracle) (fields : List Field) (world : Verity.ContractState)
    (field member : String) (key : Nat) : Option Nat :=
  evalExpr o fields { world, bindings := [("_registry_key", key)] }
    (.structMember field (.localVar "_registry_key") member)

/-- Local variable naming does not change the membership read. -/
theorem expr_read (o : DenoteOracle) (fields : List Field) (state : DenoteState)
    (field member current : String) :
    evalExpr o fields state (.structMember field (.localVar current) member) =
      read o fields state.world field member (lookupValue state.bindings current) := by
  simp [read, evalExpr, lookupValue]

/-- The storage snapshot determines membership, independently of memory and local temporaries. -/
theorem storage_frame (o : DenoteOracle) (fields : List Field)
    (before after : Verity.ContractState) (field member : String) (key : Nat)
    (storage : after.storageWords = before.storageWords) :
    read o fields after field member key = read o fields before field member key := by
  simp [read, evalExpr, lookupValue, readFieldWord, Verity.ContractState.readSlot,
    Verity.ContractState.storage,
    Verity.ContractState.readTransient, Verity.ContractState.transientStorage, storage]

/-- Nonzero mapping membership, without a reachability or configuration assumption. -/
def Registered (o : DenoteOracle) (fields : List Field) (world : Verity.ContractState)
    (field member : String) (key : Nat) : Prop :=
  ∃ value, read o fields world field member key = some value ∧ value ≠ 0

end Compiler.CompilationModel.SolidityImport.MemberRead

namespace Compiler.CompilationModel.SolidityImport.OrderedAuthorization
open Denote AuthorizationFrames

/-- Successful resolution followed by the checked guard yields one registered signer
and preserves the storage snapshot. Every premise is an executable-shape certificate. -/
theorem guarded_step (o : DenoteOracle) (fields : List Field) (snapshot : Verity.ContractState)
    (n : OrderedGuard.Names) (fresh : Function.Injective n) (field member : String) (sentinel : Nat)
    (resolution failure : List Stmt) (indexVar frameKey : String)
    (prefixProtected : protectedList (n 1) resolution = true)
    (bodyProtected : protectedList frameKey
      (resolution ++ OrderedGuard.body n field member sentinel failure) = true)
    (rejects : ∀ s t, execStmtList o fields s failure ≠ .continue t)
    (indexDifferent : indexVar ≠ n 1) (index : Nat) (state after : DenoteState)
    (unchanged : state.world.storageWords = snapshot.storageWords)
    (executed : execStmtList o fields
      { state with bindings := bindValue state.bindings indexVar (wordNormalize index) }
      (resolution ++ OrderedGuard.body n field member sentinel failure) = .continue after) :
    after.world.storageWords = snapshot.storageWords ∧
    lookupValue state.bindings (n 1) < lookupValue after.bindings (n 1) ∧
    MemberRead.Registered o fields snapshot field member (lookupValue after.bindings (n 1)) ∧
    lookupValue after.bindings (n 1) ≠ wordNormalize sentinel := by
  let initial := { state with bindings := bindValue state.bindings indexVar (wordNormalize index) }
  obtain ⟨checked, resolved, guarded⟩ := split_prefix_continue o fields initial after _ _ executed
  have preserved := protected_list_frame o fields initial resolution (n 1) prefixProtected
  have complete := protected_list_frame o fields initial _ frameKey bodyProtected
  rw [resolved] at preserved
  rw [executed] at complete
  have guard := OrderedGuard.sound o fields checked after n fresh field member sentinel failure
    rejects guarded
  refine ⟨complete.2.trans unchanged, ?_, ?_, ?_⟩
  · simpa only [guard.2.2.2, preserved.1, initial,
      lookup_bind_other _ _ _ _ indexDifferent] using guard.1
  · rw [guard.2.2.2]
    obtain ⟨value, read, nonzero⟩ := guard.2.1
    refine ⟨value, ?_, nonzero⟩
    rw [← MemberRead.storage_frame o fields snapshot checked.world field member _
      (preserved.2.trans unchanged)]
    exact (MemberRead.expr_read o fields checked field member (n 0)).symm.trans read
  · simpa only [guard.2.2.2] using guard.2.2.1

/-- Arbitrary-count authorization of the exact guarded interpreter loop. In particular,
zero iterations allow an empty resolution; wrapper positivity is proved separately. -/
theorem guarded_loop (o : DenoteOracle) (fields : List Field) (snapshot : Verity.ContractState)
    (n : OrderedGuard.Names) (fresh : Function.Injective n) (field member : String) (sentinel : Nat)
    (resolution failure : List Stmt) (indexVar frameKey : String)
    (prefixProtected : protectedList (n 1) resolution = true)
    (bodyProtected : protectedList frameKey
      (resolution ++ OrderedGuard.body n field member sentinel failure) = true)
    (rejects : ∀ s t, execStmtList o fields s failure ≠ .continue t)
    (indexDifferent : indexVar ≠ n 1) (count : Nat) (state after : DenoteState)
    (unchanged : state.world.storageWords = snapshot.storageWords)
    (zero : lookupValue state.bindings (n 1) = 0)
    (executed : execForEachLoop indexVar
      (fun s => execStmtList o fields s
        (resolution ++ OrderedGuard.body n field member sentinel failure))
      state 0 count = .continue after) :
    ∃ used, Trace indexVar (n 1)
      (fun s => execStmtList o fields s
        (resolution ++ OrderedGuard.body n field member sentinel failure))
      0 state used after ∧ used.length = count ∧ used.Nodup ∧
      ∀ signer ∈ used, MemberRead.Registered o fields snapshot field member signer ∧
        signer ≠ 0 ∧ signer ≠ wordNormalize sentinel := by
  obtain ⟨used, trace, length, ordered⟩ := loop_authorized indexVar (n 1) _
    (MemberRead.Registered o fields snapshot field member) (wordNormalize sentinel)
    (fun s => s.world.storageWords = snapshot.storageWords)
    (guarded_step o fields snapshot n fresh field member sentinel resolution failure
      indexVar frameKey
      prefixProtected bodyProtected rejects indexDifferent)
    count 0 state after unchanged executed
  rw [zero] at ordered
  exact ⟨used, trace, length, ordered_authorized _ _ used ordered⟩

end Compiler.CompilationModel.SolidityImport.OrderedAuthorization
