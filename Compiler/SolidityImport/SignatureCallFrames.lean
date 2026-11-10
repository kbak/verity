import Compiler.SolidityImport.Proofs
import Mathlib.Tactic.SplitIfs

namespace Compiler.CompilationModel.SolidityImport.AuthorizationFrames
open Denote

/-- Continuing read-only blocks preserve a protected binding; exits must revert. -/
def BindingFrame (key : String) (state : DenoteState) : StmtOutcome → Prop
  | .continue next => lookupValue next.bindings key = lookupValue state.bindings key ∧
      next.world.storageWords = state.world.storageWords
  | .revert | .invalid | .revertWithData _ => True
  | _ => False

/-- Instrumentation errors carry no successful execution. -/
def CallFrame (key : String) (state : DenoteState) :
    Except String (StmtOutcome × List Verity.StorageKey) → Prop
  | .error _ => True
  | .ok (outcome, _) => BindingFrame key state outcome

/-- Forward, possibly overlapping copy of the legacy dynamic payload. -/
def copyWords (world : Verity.ContractState) (pointer source size : Nat) : Verity.ContractState :=
  (List.range ((size + 31) / 32)).foldl (fun w i =>
    w.writePhysicalMemoryValue (pointer + 100 + i * 32)
      (Verity.Core.Uint256.ofNat (w.memory (source + i * 32)).val)) world

/-- Clean the unused final bytes after the forward copy. -/
def cleanTail (world : Verity.ContractState) (pointer size : Nat) : Verity.ContractState :=
  let rounded := ((size + 31) / 32) * 32
  let tail := pointer + 100 + rounded - 32
  if size % 32 == 0 then world else
    world.writePhysicalMemoryValue tail (Verity.Core.Uint256.ofNat
      (Nat.land (world.memory tail).val (2^256 - 2^(8 * (rounded - size)))))

/-- Opaque physical-memory preparation for the existing legacy transport. -/
def prepare (state : DenoteState) (selector : Option Nat) (values : List Nat) :
    Nat × Nat × Verity.ContractState :=
  let a := values[0]!
  let b := values[1]!
  let c := values[2]!
  let pointer := (state.world.memory 64).val
  let write := fun (w : Verity.ContractState) p n =>
    w.writePhysicalMemoryValue p (Verity.Core.Uint256.ofNat n)
  match selector with
    | none =>
      let w := write (write state.world pointer 0) 64 (pointer + 32)
      let w := values.zipIdx.foldl (fun w (n, i) => write w (pointer + 32 + i * 32) n) w
      (1, 128, w)
    | some sel =>
      let w := write (write (write state.world pointer (sel * 2^224))
        (pointer + 4) b) (pointer + 36) 64
      let d := (w.memory (wordNormalize (c + 2^256 - 32))).val
      let w := write w (pointer + 68) d
      let rounded := ((d + 31) / 32) * 32
      let w := (List.range ((d + 31) / 32)).foldl (fun w i =>
        write w (pointer + 100 + i * 32) (w.memory (c + i * 32)).val) w
      let tail := pointer + 100 + rounded - 32
      let w := if d % 32 == 0 then w else
        write w tail (Nat.land (w.memory tail).val (2^256 - 2^(8 * (rounded - d))))
      (a % 2^160, 100 + rounded, w)

/-- The response continuation has no successful early exit. -/
def finish (state : DenoteState) (result : String) (selector : Option Nat) (pointer : Nat)
    (response : ByteExternalCall.Observation Verity.ContractState Verity.StorageKey) :
    Except String (StmtOutcome × List Verity.StorageKey) := do
  if !response.success then return (.revertWithData response.returndata, response.touched)
  if selector.isSome && response.returndata.length < 32 then
    return (.revertWithData [], response.touched)
  let world := response.world.copyPhysicalMemory (rawPhysicalByte response.returndata)
    pointer 0 (min 32 response.returndata.length)
  let mask := if selector.isSome then (2^32 - 1) * 2^224 else 2^160 - 1
  let value := Nat.land (world.memory pointer).val mask
  return (.continue { state with
    world := world
    bindings := bindValue state.bindings result value
    rawReturndata := some response.returndata
    byteCallAccesses := state.byteCallAccesses ++ response.touched }, response.touched)

/-- Transport after checking argument availability. -/
def preparedCall (state : DenoteState) (result : String) (selector : Option Nat)
    (gas : Nat) (adversary : ByteExternalCall.Adversary Verity.ContractState Verity.StorageKey)
    (values : List Nat) : Except String (StmtOutcome × List Verity.StorageKey) := do
  let pointer := (state.world.memory 64).val
  let (target, size, prepared) := prepare state selector values
  if selector.isSome && DenoteExternalCode.extCodeSize prepared
      (Verity.Core.Address.ofNat target) == 0 then
    return (.revertWithData [], [])
  let input := if selector.isSome then pointer else pointer + 32
  let request : ByteExternalCall.Request := {
    kind := .staticcall, caller := prepared.thisAddress.val, target, value := 0, gas,
    calldata := (List.range size).map fun i => UInt8.ofNat (prepared.physicalByte (input + i)).val }
  let response ← ByteExternalCall.executeChecked adversary request prepared
  finish state result selector pointer response

/-- A definitional decomposition of the interpreter, with no replacement semantics. -/
theorem legacy_call_eq (o : DenoteOracle) (fs : List Field) (state : DenoteState)
    (mod : Compiler.ECM.ExternalCallModule) (result : String) (selector : Option Nat)
    (args : List Expr) :
    executeLegacySignatureCall o fs state mod result selector args = (do
      let expected := match selector with
        | none => Compiler.ECM.LegacySignatureCall.recoverModule result
        | some sel => Compiler.ECM.LegacySignatureCall.bytes4Module result sel
      unless mod == expected do throw "closed legacy signature transport metadata differs"
      let some adversary := state.byteCallAdversary | throw "legacy call adversary missing"
      let some gas := state.byteCallGas | throw "legacy call gas environment missing"
      let some values := evalExprList o fs state args
        | throw "legacy call argument evaluation unsupported"
      unless values.length == (if selector.isSome then 3 else 4) do
        throw "legacy call argument count differs"
      preparedCall state result selector gas adversary values) := by rfl

/-- Scratch-memory writes leave the account storage view unchanged. -/
@[simp] theorem memory_storage (world : Verity.ContractState) (offset : Nat)
    (value : Verity.Core.Uint256) :
    (world.writePhysicalMemoryValue offset value).storageWords = world.storageWords := rfl

/-- Byte copies also preserve account storage. -/
@[simp] theorem copy_storage (world : Verity.ContractState)
    (source : Nat → Fin 256)
    (destination start size : Nat) :
    (world.copyPhysicalMemory source destination start size).storageWords =
      world.storageWords := rfl

/-- Pointwise storage frames compose through memory-copy folds. -/
theorem foldl_storage (f : Verity.ContractState → α → Verity.ContractState)
    (items : List α) (world : Verity.ContractState)
    (preserves : ∀ state item, (f state item).storageWords = state.storageWords) :
    (items.foldl f world).storageWords = world.storageWords := by
  induction items generalizing world with
  | nil => rfl
  | cons item rest ih => exact (ih (f world item)).trans (preserves world item)

/-- Every forward-copy iteration preserves storage, including overlapping copies. -/
@[simp] theorem copy_words_storage (world : Verity.ContractState) (pointer source size : Nat) :
    (copyWords world pointer source size).storageWords = world.storageWords := by
  exact foldl_storage _ _ _ (by intros; rfl)

/-- Clearing tail bytes preserves storage. -/
@[simp] theorem clean_tail_storage (world : Verity.ContractState) (pointer size : Nat) :
    (cleanTail world pointer size).storageWords = world.storageWords := by
  unfold cleanTail
  split_ifs <;> rfl

/-- The exact legacy ABI preparation only writes scratch memory. -/
theorem prepare_storage (state : DenoteState) (selector : Option Nat) (values : List Nat) :
    (prepare state selector values).2.2.storageWords = state.world.storageWords := by
  cases selector with
  | none => exact foldl_storage _ _ _ (by intros; rfl)
  | some selector =>
      change (cleanTail _ _ _).storageWords = state.world.storageWords
      rw [clean_tail_storage]
      change (copyWords _ _ _ _).storageWords = state.world.storageWords
      rw [copy_words_storage]
      simp only [memory_storage]

/-- The checked STATICCALL boundary enforces the adversary's world-frame proof. -/
theorem checked_static_storage
    (adversary : ByteExternalCall.Adversary Verity.ContractState Verity.StorageKey)
    (request : ByteExternalCall.Request) (world : Verity.ContractState)
    (response : ByteExternalCall.Observation Verity.ContractState Verity.StorageKey)
    (kind : request.kind = .staticcall)
    (executed : ByteExternalCall.executeChecked adversary request world = .ok response) :
    response.world.storageWords = world.storageWords := by
  cases h : adversary.accepts request world with
  | false => rw [ByteExternalCall.executeChecked_rejects _ _ _ h] at executed; cases executed
  | true =>
      rw [ByteExternalCall.executeChecked_agrees _ _ _ h] at executed
      cases executed
      exact congrArg Verity.ContractState.storageWords
        (ByteExternalCall.execute_static_world adversary request world kind)

/-- Only the selected result binding changes after either legacy static transport. -/
theorem finish_frame (state : DenoteState) (result key : String) (selector : Option Nat)
    (pointer : Nat) (response : ByteExternalCall.Observation Verity.ContractState Verity.StorageKey)
    (distinct : result ≠ key) (storage : response.world.storageWords = state.world.storageWords) :
    CallFrame key state (finish state result selector pointer response) := by
  unfold finish
  split_ifs <;> simp [bind, Except.bind, pure, Except.pure, CallFrame, BindingFrame,
    lookup_bind_other _ _ _ _ distinct, storage]

/-- Memory preparation and the static child cannot alter local bindings. -/
theorem prepared_frame (state : DenoteState) (result key : String) (selector : Option Nat)
    (gas : Nat) (adversary : ByteExternalCall.Adversary Verity.ContractState Verity.StorageKey)
    (values : List Nat) (distinct : result ≠ key) :
    CallFrame key state (preparedCall state result selector gas adversary values) := by
  unfold preparedCall
  have storage := prepare_storage state selector values
  generalize prepared : prepare state selector values = tuple at *
  rcases tuple with ⟨target, size, world⟩
  dsimp only
  split_ifs <;> simp only [bind, Except.bind, pure, Except.pure]
  all_goals first
    | trivial
    | (generalize executed : ByteExternalCall.executeChecked adversary _ world = response
       cases response with
       | error message => trivial
       | ok response =>
           exact finish_frame state result key selector _ response distinct
             ((checked_static_storage adversary _ world response rfl executed).trans storage))

/-- The closed legacy transports write only their named result binding. -/
theorem legacy_call_frame (o : DenoteOracle) (fs : List Field) (state : DenoteState)
    (mod : Compiler.ECM.ExternalCallModule) (result key : String) (selector : Option Nat)
    (args : List Expr) (distinct : result ≠ key) :
    CallFrame key state (executeLegacySignatureCall o fs state mod result selector args) := by
  rw [legacy_call_eq]
  cases state.byteCallAdversary <;> cases state.byteCallGas <;>
    cases evalExprList o fs state args <;>
    dsimp only [bind, Except.bind, pure, Except.pure, throw]
  all_goals split_ifs
  all_goals try dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe]
  all_goals first
    | exact prepared_frame state result key selector _ _ _ distinct
    | trivial
end Compiler.CompilationModel.SolidityImport.AuthorizationFrames
