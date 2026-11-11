import Compiler.SolidityImport.OrderedAuthorization

namespace Compiler.CompilationModel.SolidityImport.OrderedAuthorization
open Denote AuthorizationFrames

/-- A structurally checked prefix cannot supply a successful early return. -/
theorem stop_prefix (o : DenoteOracle) (fields : List Field) (state final : DenoteState)
    (pre suffix : List Stmt) (key : String) (accepted : protectedList key pre = true)
    (executed : execStmtList o fields state (pre ++ suffix) = .stop final) :
    ∃ middle, execStmtList o fields state pre = .continue middle ∧
      execStmtList o fields middle suffix = .stop final := by
  have frame := protected_list_frame o fields state pre key accepted
  rw [exec_append] at executed
  cases h : execStmtList o fields state pre with
  | «continue» middle => exact ⟨middle, rfl, by simpa only [h] using executed⟩
  | stop middle => simp [h, BindingFrame] at frame
  | «return» value middle => simp [h, BindingFrame] at frame
  | revert => simp [h] at executed
  | revertWithData bytes => simp [h] at executed
  | invalid => simp [h] at executed

/-- Successful assignment followed by a suffix exposes the exact evaluated value. -/
theorem let_continue (o : DenoteOracle) (fields : List Field) (state final : DenoteState)
    (name : String) (value : Expr) (rest : List Stmt)
    (executed : execStmtList o fields state (.letVar name value :: rest) = .continue final) :
    ∃ resolved, evalExpr o fields state value = some resolved ∧
      execStmtList o fields { state with bindings := bindValue state.bindings name resolved }
        rest = .continue final := by
  rw [exec_let_cons] at executed
  cases h : evalExpr o fields state value with
  | none => simp [h] at executed
  | some resolved => exact ⟨resolved, rfl, by simpa only [h] using executed⟩

/-- The actual loop statement freezes its evaluated bound before binding the first index. -/
theorem foreach_continue (o : DenoteOracle) (fields : List Field) (state final : DenoteState)
    (index : String) (count : Expr) (body : List Stmt)
    (executed : execStmt o fields state (.forEach index count body) = .continue final) :
    ∃ bound, evalExpr o fields state count = some bound ∧
      execForEachLoop index (fun s => execStmtList o fields s body)
        { state with bindings := bindValue state.bindings index (wordNormalize 0) }
        0 bound = .continue final := by
  cases h : evalExpr o fields state count with
  | none => simp [execStmt, h] at executed
  | some bound => exact ⟨bound, rfl, by simpa only [execStmt, h] using executed⟩

/-- Continuing setup preserves both a frozen count and a zero preceding signer. -/
theorem setup_values (o : DenoteOracle) (fields : List Field) (state ready : DenoteState)
    (setup : List Stmt) (countName previous : String) (count : Nat)
    (different : previous ≠ countName)
    (countFrame : protectedList countName setup = true)
    (previousFrame : protectedList previous setup = true)
    (initialCount : lookupValue state.bindings countName = count)
    (executed : execStmtList o fields
      { state with bindings := bindValue state.bindings previous 0 } setup = .continue ready) :
    lookupValue ready.bindings previous = 0 ∧ lookupValue ready.bindings countName = count ∧
      ready.world.storageWords = state.world.storageWords := by
  let initialized := { state with bindings := bindValue state.bindings previous 0 }
  have hp := protected_list_frame o fields initialized setup previous previousFrame
  have hc := protected_list_frame o fields initialized setup countName countFrame
  rw [executed] at hp hc
  exact ⟨hp.1.trans (lookup_bind_same _ _ _),
    hc.1.trans ((lookup_bind_other _ _ _ _ different).trans initialCount), hp.2⟩

/-- Extract the reached loop after count initialization, retaining the actual setup execution. -/
theorem reach_loop (o : DenoteOracle) (fields : List Field) (state final : DenoteState)
    (middle setup body tail : List Stmt) (countName previous indexVar : String) (count : Nat)
    (different : previous ≠ countName)
    (middleFrame : protectedList countName middle = true)
    (countFrame : protectedList countName setup = true)
    (previousFrame : protectedList previous setup = true)
    (initialCount : lookupValue state.bindings countName = count)
    (executed : execStmtList o fields state (middle ++ (.letVar previous (.literal 0) ::
      (setup ++ (.forEach indexVar (.localVar countName) body :: tail)))) = .continue final) :
    ∃ (before ready loopAfter : DenoteState),
      execStmtList o fields state middle = .continue before ∧
      execStmtList o fields
        { before with bindings := bindValue before.bindings previous 0 } setup = .continue ready ∧
      lookupValue ready.bindings previous = 0 ∧
      ready.world.storageWords = state.world.storageWords ∧
      execForEachLoop indexVar (fun s => execStmtList o fields s body)
        { ready with bindings := bindValue ready.bindings indexVar (wordNormalize 0) }
        0 count = .continue loopAfter := by
  obtain ⟨before, first, rest⟩ := split_prefix_continue o fields state final _ _ executed
  have frame := protected_list_frame o fields state middle countName middleFrame
  rw [first] at frame
  rw [exec_let_cons] at rest
  change execStmtList o fields { before with bindings := bindValue before.bindings previous 0 }
    (setup ++ (.forEach indexVar (.localVar countName) body :: tail)) = .continue final at rest
  obtain ⟨ready, prepared, rest⟩ := split_prefix_continue o fields _ final _ _ rest
  obtain ⟨loopAfter, loopStep, _⟩ := split_prefix_continue o fields ready final [_] tail rest
  rw [exec_singleton] at loopStep
  have values := setup_values o fields before ready setup countName previous count different
    countFrame previousFrame (frame.1.trans initialCount) prepared
  obtain ⟨bound, evaluated, ran⟩ :=
    foreach_continue o fields ready loopAfter indexVar _ body loopStep
  have boundEq : count = bound := by simpa only [OrderedGuard.eval_local, values.2.1,
    Option.some.injEq] using evaluated
  exact ⟨before, ready, loopAfter, first, prepared, values.1,
    values.2.2.trans frame.2, boundEq.symm ▸ ran⟩

end Compiler.CompilationModel.SolidityImport.OrderedAuthorization

namespace Compiler.CompilationModel.SolidityImport.OrderedAuthorization
open Denote AuthorizationFrames

/-- Parameters of the exact resolved-signer guard and loop. -/
structure Guard where
  names : OrderedGuard.Names
  field : String
  member : String
  sentinel : Nat
  resolution : List Stmt
  failure : List Stmt
  indexVar : String
  frameKey : String

/-- The actual loop body, including signature resolution. -/
def Guard.body (guard : Guard) : List Stmt :=
  guard.resolution ++
    OrderedGuard.body guard.names guard.field guard.member guard.sentinel guard.failure

/-- Kernel-checkable structural obligations; rejection is supplied by the closed revert theorem. -/
structure Guard.Certificate (o : DenoteOracle) (fields : List Field) (guard : Guard) : Prop where
  fresh : Function.Injective guard.names
  resolutionProtected : protectedList (guard.names 1) guard.resolution = true
  bodyProtected : protectedList guard.frameKey guard.body = true
  rejects : ∀ state after, execStmtList o fields state guard.failure ≠ .continue after
  indexDifferent : guard.indexVar ≠ guard.names 1

/-- Entry layout: initialize and check the count, initialize the preceding signer, then loop. -/
structure Program where
  guard : Guard
  countName : String
  countExpr : Expr
  start : List Stmt
  middle : List Stmt
  setup : List Stmt
  tail : List Stmt
  returns : List Expr

/-- Everything before the final return, retaining the source's evaluation order. -/
def Program.pre (program : Program) : List Stmt :=
  program.start ++ (.letVar program.countName program.countExpr ::
    (program.middle ++ (.letVar (program.guard.names 1) (.literal 0) ::
      (program.setup ++ (.forEach program.guard.indexVar (.localVar program.countName)
        program.guard.body :: program.tail)))))

/-- The complete imported entrypoint body. -/
def Program.body (program : Program) : List Stmt := program.pre ++ [.returnValues program.returns]

/-- Structural certificates for count preservation and exclusion of early successful exits. -/
structure Program.Certificate (o : DenoteOracle) (fields : List Field)
    (program : Program) : Prop where
  guard : program.guard.Certificate o fields
  countDifferent : program.guard.names 1 ≠ program.countName
  preProtected : protectedList program.guard.frameKey program.pre = true
  startProtected : protectedList program.guard.frameKey program.start = true
  middleProtected : protectedList program.countName program.middle = true
  setupCount : protectedList program.countName program.setup = true
  setupPrevious : protectedList (program.guard.names 1) program.setup = true

/-- Authorization evidence records the reached count read and the actual signer trace.
The wrapper can separately connect the count read to its stored threshold and prove positivity. -/
structure EntryEvidence (o : DenoteOracle) (fields : List Field) (program : Program)
    (state : DenoteState) where
  count : Nat
  beforeCount : DenoteState
  beforeInit : DenoteState
  ready : DenoteState
  loopStart : DenoteState
  loopAfter : DenoteState
  used : List Nat
  reachedCount : execStmtList o fields state program.start = .continue beforeCount
  countRead : evalExpr o fields beforeCount program.countExpr = some count
  countStorage : beforeCount.world.storageWords = state.world.storageWords
  checkedMiddle : execStmtList o fields
    { beforeCount with bindings := bindValue beforeCount.bindings program.countName count }
    program.middle = .continue beforeInit
  setupReached : execStmtList o fields
    { beforeInit with bindings := bindValue beforeInit.bindings (program.guard.names 1) 0 }
    program.setup = .continue ready
  loopInitialized : loopStart =
    { ready with bindings := bindValue ready.bindings program.guard.indexVar (wordNormalize 0) }
  trace : Trace program.guard.indexVar (program.guard.names 1)
    (fun s => execStmtList o fields s program.guard.body) 0 loopStart used loopAfter
  cardinality : used.length = count
  distinct : used.Nodup
  members : ∀ signer ∈ used,
    MemberRead.Registered o fields state.world program.guard.field program.guard.member signer ∧
      signer ≠ 0 ∧ signer ≠ wordNormalize program.guard.sentinel

/-- A complete successful entry yields exactly the counted distinct registered signers. -/
theorem entry_authorized (o : DenoteOracle) (fields : List Field) (p : Program)
    (certificate : p.Certificate o fields) (state final : DenoteState)
    (executed : execStmtList o fields state p.body = .stop final) :
    Nonempty (EntryEvidence o fields p state) := by
  obtain ⟨finished, prefixRan, _⟩ := stop_prefix o fields state final p.pre [_]
    p.guard.frameKey certificate.preProtected executed
  obtain ⟨beforeCount, startRan, rest⟩ :=
    split_prefix_continue o fields state finished _ _ prefixRan
  obtain ⟨count, countRead, counted⟩ := let_continue o fields beforeCount finished _ _ _ rest
  let countState :=
    { beforeCount with bindings := bindValue beforeCount.bindings p.countName count }
  have startFrame := protected_list_frame o fields state p.start p.guard.frameKey
    certificate.startProtected
  rw [startRan] at startFrame
  obtain ⟨beforeInit, ready, loopAfter, checkedMiddle, prepared, zero, storage, ran⟩ :=
    reach_loop o fields countState finished p.middle p.setup p.guard.body p.tail
      p.countName (p.guard.names 1) p.guard.indexVar count certificate.countDifferent
      certificate.middleProtected certificate.setupCount certificate.setupPrevious
      (lookup_bind_same _ _ _) counted
  let loopStart :=
    { ready with bindings := bindValue ready.bindings p.guard.indexVar (wordNormalize 0) }
  have initialZero : lookupValue loopStart.bindings (p.guard.names 1) = 0 :=
    (lookup_bind_other _ _ _ _ certificate.guard.indexDifferent).trans zero
  obtain ⟨used, trace, length, distinct, members⟩ := guarded_loop o fields state.world
    p.guard.names certificate.guard.fresh p.guard.field p.guard.member p.guard.sentinel
    p.guard.resolution p.guard.failure p.guard.indexVar p.guard.frameKey
    certificate.guard.resolutionProtected certificate.guard.bodyProtected certificate.guard.rejects
    certificate.guard.indexDifferent count loopStart loopAfter
    (storage.trans startFrame.2) initialZero ran
  exact ⟨⟨count, beforeCount, beforeInit, ready, loopStart, loopAfter, used, startRan,
    countRead, startFrame.2, checkedMiddle, prepared, rfl, trace, length, distinct, members⟩⟩

end Compiler.CompilationModel.SolidityImport.OrderedAuthorization

namespace Compiler.CompilationModel.SolidityImport.OrderedAuthorization
open Denote AuthorizationFrames

/-- A lowered zero-count rejection gate, before any signature-loop work. -/
def zeroGate (countName flag : String) (failure : List Stmt) : List Stmt :=
  [.letVar flag (.eq (.localVar countName) (.literal 0)), .ite (.localVar flag) failure []]

/-- A successful zero-count gate establishes a positive count; no positivity is assumed. -/
theorem gate_positive (o : DenoteOracle) (fields : List Field) (state after : DenoteState)
    (countName flag : String) (failure : List Stmt)
    (rejects : ∀ before final, execStmtList o fields before failure ≠ .continue final)
    (executed : execStmtList o fields state (zeroGate countName flag failure) = .continue after) :
    0 < lookupValue state.bindings countName := by
  apply Nat.pos_of_ne_zero
  intro zero
  simp [zeroGate, exec_let_cons, execStmt, OrderedGuard.eval_eq, OrderedGuard.eval_local,
    OrderedGuard.eval_literal, boolWord, lookup_bind_same, zero] at executed
  exact rejects _ _ executed

/-- A scalar storage value read through the imported field layout. -/
def storageValue (o : DenoteOracle) (fields : List Field) (world : Verity.ContractState)
    (field : String) : Option Nat := evalExpr o fields { world, bindings := [] } (.storage field)

/-- A storage count read is independent of local bindings and call instrumentation. -/
theorem storage_expr (o : DenoteOracle) (fields : List Field)
    (state : DenoteState) (field : String) :
    evalExpr o fields state (.storage field) = storageValue o fields state.world field := rfl

/-- The entry's storage frame pins the count to the initial storage snapshot. -/
theorem storage_value_frame (o : DenoteOracle) (fields : List Field)
    (before after : Verity.ContractState) (field : String)
    (storage : after.storageWords = before.storageWords) :
    storageValue o fields after field = storageValue o fields before field := by
  simp [storageValue, evalExpr, readFieldWord, Verity.ContractState.readSlot,
    Verity.ContractState.storage, Verity.ContractState.readTransient,
    Verity.ContractState.transientStorage, storage]

/-- A stored count is the initial stored count, even after memory allocation and validation. -/
theorem evidence_stored_count (o : DenoteOracle) (fields : List Field) (program : Program)
    (state : DenoteState) (evidence : EntryEvidence o fields program state) (field : String)
    (source : program.countExpr = .storage field) :
    storageValue o fields state.world field = some evidence.count := by
  have read := evidence.countRead
  rw [source, storage_expr,
    storage_value_frame o fields state.world evidence.beforeCount.world field
    evidence.countStorage] at read
  exact read

/-- Wrapper positivity follows from its reached rejection gate, independently of the loop. -/
theorem evidence_positive (o : DenoteOracle) (fields : List Field) (program : Program)
    (state : DenoteState) (evidence : EntryEvidence o fields program state)
    (flag : String) (failure rest : List Stmt)
    (shape : program.middle = zeroGate program.countName flag failure ++ rest)
    (rejects : ∀ before final, execStmtList o fields before failure ≠ .continue final) :
    0 < evidence.count := by
  have reached := evidence.checkedMiddle
  rw [shape] at reached
  obtain ⟨after, executed, _⟩ := split_prefix_continue o fields _ _ _ _ reached
  have positive := gate_positive o fields _ after program.countName flag failure rejects executed
  simpa only [lookup_bind_same] using positive

end Compiler.CompilationModel.SolidityImport.OrderedAuthorization
