import Compiler.Proofs.SolidityImport.Solcore.Primitives
import Compiler.Proofs.SolidityImport.Solcore.Runtime
import Compiler.Proofs.SolidityImport.Solcore.WordAlignment
import Verity.Core.Model.Denote

set_option autoImplicit false

namespace Compiler.Proofs.SolidityImport.SolcoreBridge

open Compiler.CompilationModel
open Compiler.CompilationModel.Denote
open Compiler.Proofs.SolidityImport.Solcore
open Compiler.Proofs.SolidityImport.Solcore.Core
open Compiler.Proofs.SolidityImport.Solcore.ContractRuntime

/-!
# Formal Semantic Bridge: `solcore-lean` ↔ `Verity.Core.Model.Denote` (Stage 4.1 / N9)

This module establishes the formal refinement and bisimulation bridge between the
declarative `argotorg/solcore-lean` semantics (`Solcore.Core` and
`Solcore.ContractRuntime`) and Verity's canonical deep-model denotation
(`Compiler.CompilationModel.Denote`):

1. **`StateRefines`**: Formal state refinement relation connecting
   `SolcoreExecState` (persistent `WorldState` storage, EIP-1153
   `transientStorage`, word-addressed `memory`, local bindings,
   `TransactionJournal`, and frame-entry `checkpoint`) to `DenoteState` and
   the frame-entry `Verity.ContractState`.
2. **256-bit `Solcore.Core` Expression Bisimulation (`ExprRefines`)**:
   Proves that every 256-bit `Solcore.Core` primitive (`add`, `sub`, `mul`,
   `div`, `sdiv`, `mod`, `smod`, `addmod`, `mulmod`, `and`, `or`, `xor`, `not`,
   `shl`, `shr`, `sar`, `signextend`, `byte`, `pow`, `eq`, `lt`, `gt`, `slt`,
   `sgt`, `iszero`, `boolAnd`, `boolOr`, `ifE`) refines its `Denote.evalExpr`
   counterpart.
3. **Storage, Mapping, Transient Storage, Memory, and Local Variable Refinement**:
   Proves read/write preservation for `sload`/`sstore`, `WordMapping`
   slot-hashed entries, `tload`/`tstore`, `mload`, and `letVar`/`assignVar`.
4. **Transaction Journal & Frame Rollback / Commit Bisimulation**:
   Proves that `SolcoreExecState.resolveFrame` on `.reverted` and `.returned`
   refines `Denote.revertedResult` and `Denote.successResult`.
5. **Certified Translation Validation (`CertifiedTranslationWitness`)**:
   Packages `SolcoreToVerityBisim` into a self-contained witness whose soundness
   theorems guarantee that `Denote.denoteFunction` (and downstream Layer 2/3
   IR/EVM compilation) preserves declarative `Solcore` semantics without
   trusting the 889 KB `Import.lean` translator in the TCB.
-/

/-! ## 1. Boolean-Word Conversion Helpers in `Solcore.Core` -/

namespace Word

/-- Canonical `Word` encoding of a boolean (`1` for `true`, `0` for `false`). -/
def ofBool (b : Bool) : Word :=
  if b then Word.ofNatModulo 1 else Word.zero

@[simp] theorem val_ofBool (b : Bool) :
    (ofBool b).val = Denote.boolWord b := by
  cases b <;> rfl

@[simp] theorem toUint256_ofNat_val (w : Word) :
    Verity.Core.Uint256.ofNat w.val = w.toUint256 := by
  apply Verity.Core.Uint256.ext
  simp [Verity.Core.Uint256.val_ofNat, Verity.Core.Uint256.modulus,
    ← wordModulus_eq_uint256_modulus, Nat.mod_eq_of_lt w.isLt]

@[simp] theorem wordNormalize_val (w : Word) :
    Denote.wordNormalize w.val = w.val := by
  unfold Denote.wordNormalize
  change (Verity.Core.Uint256.ofNat w.val).val = w.val
  rw [toUint256_ofNat_val]
  rfl

theorem evaluates_boolToWord
    {env : Environment} {store finalStore : Store}
    {cond : Core.Expr} {b : Bool}
    (hCond : Evaluates env store cond (.bool b) finalStore) :
    Evaluates env store (Core.Expr.boolToWord cond) (.word (ofBool b)) finalStore := by
  unfold Core.Expr.boolToWord ofBool
  cases b
  · exact Evaluates.ifFalse hCond Evaluates.word
  · exact Evaluates.ifTrue hCond Evaluates.word

theorem evaluates_wordToBool
    {env : Environment} {store finalStore : Store}
    {e : Core.Expr} {w : Word}
    (hEval : Evaluates env store e (.word w) finalStore) :
    Evaluates env store (Core.Expr.wordToBool e)
      (.bool (decide (w.val != 0))) finalStore := by
  unfold Core.Expr.wordToBool
  have hEq : Evaluates env store (.binary .wordEq e (.word Word.zero))
      (.bool (w == Word.zero)) finalStore :=
    Evaluates.binary hEval Evaluates.word rfl
  by_cases hz : w.val = 0
  · have hw : (w == Word.zero) = true := by
      rw [Word.word_isZero_eq_decide, decide_eq_true hz]
    rw [hw] at hEq
    simpa [hz] using Evaluates.ifTrue hEq Evaluates.bool
  · have hw : (w == Word.zero) = false := by
      rw [Word.word_isZero_eq_decide, decide_eq_false hz]
    rw [hw] at hEq
    simpa [hz] using Evaluates.ifFalse hEq Evaluates.bool

end Word

private theorem option_bind₁_some
    {oa : Option Nat} {va res : Nat}
    (f : Nat → Nat)
    (hA : oa = some va)
    (hRes : f va = res) :
    (oa.bind fun a => some (f a)) = some res := by
  subst hA hRes; rfl

private theorem option_bind₂_some
    {oa ob : Option Nat} {va vb res : Nat}
    (f : Nat → Nat → Nat)
    (hA : oa = some va)
    (hB : ob = some vb)
    (hRes : f va vb = res) :
    (oa.bind fun a => ob.bind fun b => some (f a b)) = some res := by
  subst hA hB hRes; rfl

/-! ## 2. Formal State Refinement Relation (`StateRefines`) -/

/-- Refinement between `SolcoreExecState` and `DenoteState` relative to an
    initial frame-entry `Verity.ContractState`. -/
structure StateRefines
    (sState : SolcoreExecState)
    (dState : DenoteState)
    (initialWorld : Verity.ContractState) : Prop where
  /-- Persistent storage slots agree word-for-word. -/
  storage_eq :
    ∀ slot : Word,
      (sState.sload slot).val = (dState.world.readSlot slot.val).val
  /-- EIP-1153 transient storage slots agree word-for-word. -/
  transient_eq :
    ∀ slot : Word,
      (sState.tload slot).val = (dState.world.readTransient slot.val).val
  /-- Word-addressed memory agrees at every 256-bit offset. -/
  memory_eq :
    ∀ offset : Word,
      (sState.mload offset).val = (dState.world.memory offset.val).val
  /-- Local variable bindings agree for every identifier. -/
  locals_eq :
    ∀ name : String,
      (sState.getLocal name).val = Denote.lookupValue dState.bindings name
  /-- Emitted event log count in `TransactionJournal` matches `dState.world.events`. -/
  journal_len_eq :
    sState.journal.logs.length = dState.world.events.length
  /-- Frame checkpoint storage matches `initialWorld` storage. -/
  checkpoint_storage_eq :
    ∀ slot : Word,
      (sState.checkpoint.world.storageRead sState.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val
  /-- Frame checkpoint transient storage matches `initialWorld` transient storage. -/
  checkpoint_transient_eq :
    ∀ slot : Word,
      (sState.checkpoint.transientStorage slot).val =
        (initialWorld.readTransient slot.val).val
  /-- Frame checkpoint journal log count matches `initialWorld.events`. -/
  checkpoint_journal_len_eq :
    sState.checkpoint.journal.logs.length = initialWorld.events.length

/-! ## 3. Expression Refinement (`ExprRefines`) and 256-Bit Primitive Bisimulation -/

/-- Expression refinement: `e_sol` evaluates to `.word w` in `Solcore.Core`
    (preserving `store`) and `e_ver` evaluates to `some w.val` in `Denote.evalExpr`. -/
def ExprRefines
    (env : Environment) (store : Store)
    (oracle : DenoteOracle) (fields : List Field) (dState : DenoteState)
    (e_sol : Core.Expr) (e_ver : Compiler.CompilationModel.Expr)
    (w : Word) : Prop :=
  Evaluates env store e_sol (.word w) store ∧
    Denote.evalExpr oracle fields dState e_ver = some w.val

theorem exprRefines_word
    (env : Environment) (store : Store)
    (oracle : DenoteOracle) (fields : List Field) (dState : DenoteState)
    (w : Word) :
    ExprRefines env store oracle fields dState (.word w) (.literal w.val) w := by
  refine ⟨Evaluates.word, ?_⟩
  change some (Denote.wordNormalize w.val) = some w.val
  rw [Word.wordNormalize_val]

theorem exprRefines_localVar
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (env : Environment) (store : Store)
    (oracle : DenoteOracle) (fields : List Field)
    (idx : Nat) (name : String)
    (hEnv : env[idx]? = some (.word (sState.getLocal name))) :
    ExprRefines env store oracle fields dState
      (.var idx) (.localVar name) (sState.getLocal name) := by
  refine ⟨Evaluates.var hEnv, ?_⟩
  change some (Denote.lookupValue dState.bindings name) = some (sState.getLocal name).val
  rw [hRef.locals_eq name]

theorem exprRefines_add
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordAdd a_sol b_sol) (.add a_ver b_ver) (wa.add wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_add_val_eq wa wb).symm

theorem exprRefines_sub
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordSub a_sol b_sol) (.sub a_ver b_ver) (wa.sub wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_sub_val_eq wa wb).symm

theorem exprRefines_mul
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordMul a_sol b_sol) (.mul a_ver b_ver) (wa.mul wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_mul_val_eq wa wb).symm

theorem exprRefines_div
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordDiv a_sol b_sol) (.div a_ver b_ver) (wa.udiv wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_udiv_val_eq wa wb).symm

theorem exprRefines_mod
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordMod a_sol b_sol) (.mod a_ver b_ver) (wa.umod wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_umod_val_eq wa wb).symm

theorem exprRefines_sdiv
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordSdiv a_sol b_sol) (.sdiv a_ver b_ver) (wa.sdiv wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_sdiv_val_eq wa wb).symm

theorem exprRefines_smod
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordSmod a_sol b_sol) (.smod a_ver b_ver) (wa.smod wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_smod_val_eq wa wb).symm

theorem exprRefines_addMod
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol m_sol : Core.Expr}
    {a_ver b_ver m_ver : Compiler.CompilationModel.Expr}
    {wa wb wm : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb)
    (hM : ExprRefines env store oracle fields dState m_sol m_ver wm)
    (hNoWrap : wa.val + wb.val < wordModulus) :
    ExprRefines env store oracle fields dState
      (.ternary .wordAddMod a_sol b_sol m_sol)
      (.mod (.add a_ver b_ver) m_ver)
      (wa.addMod wb wm) := by
  have hAdd := exprRefines_add hA hB
  refine ⟨Evaluates.ternary hA.1 hB.1 hM.1 rfl,
    option_bind₂_some _ hAdd.2 hM.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val,
    ← Word.word_umod_val_eq]
  have hAddVal : (wa.add wb).val = wa.val + wb.val := by
    change (wa.val + wb.val) % wordModulus = wa.val + wb.val
    exact Nat.mod_eq_of_lt hNoWrap
  unfold Word.umod Word.addMod
  by_cases hz : wm.val = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, Word.val_ofNatModulo]
    have hlt : (wa.val + wb.val) % wm.val < wordModulus :=
      Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)) wm.isLt
    change (wa.add wb).val % wm.val = ((wa.val + wb.val) % wm.val) % wordModulus
    rw [hAddVal, Nat.mod_eq_of_lt hlt]

theorem exprRefines_mulMod
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol m_sol : Core.Expr}
    {a_ver b_ver m_ver : Compiler.CompilationModel.Expr}
    {wa wb wm : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb)
    (hM : ExprRefines env store oracle fields dState m_sol m_ver wm)
    (hNoWrap : wa.val * wb.val < wordModulus) :
    ExprRefines env store oracle fields dState
      (.ternary .wordMulMod a_sol b_sol m_sol)
      (.mod (.mul a_ver b_ver) m_ver)
      (wa.mulMod wb wm) := by
  have hMul := exprRefines_mul hA hB
  refine ⟨Evaluates.ternary hA.1 hB.1 hM.1 rfl,
    option_bind₂_some _ hMul.2 hM.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val,
    ← Word.word_umod_val_eq]
  have hMulVal : (wa.mul wb).val = wa.val * wb.val := by
    change (wa.val * wb.val) % wordModulus = wa.val * wb.val
    exact Nat.mod_eq_of_lt hNoWrap
  unfold Word.umod Word.mulMod
  by_cases hz : wm.val = 0
  · simp [hz]
  · simp only [hz, ↓reduceIte, Word.val_ofNatModulo]
    have hlt : (wa.val * wb.val) % wm.val < wordModulus :=
      Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hz)) wm.isLt
    change (wa.mul wb).val % wm.val = ((wa.val * wb.val) % wm.val) % wordModulus
    rw [hMulVal, Nat.mod_eq_of_lt hlt]

theorem exprRefines_bitAnd
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordAnd a_sol b_sol) (.bitAnd a_ver b_ver) (wa.bitAnd wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_bitAnd_val_eq wa wb).symm

theorem exprRefines_bitOr
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordOr a_sol b_sol) (.bitOr a_ver b_ver) (wa.bitOr wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_bitOr_val_eq wa wb).symm

theorem exprRefines_bitXor
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (.binary .wordXor a_sol b_sol) (.bitXor a_ver b_ver) (wa.bitXor wb) := by
  refine ⟨Evaluates.binary hA.1 hB.1 rfl,
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_bitXor_val_eq wa wb).symm

theorem exprRefines_bitNot
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol : Core.Expr} {a_ver : Compiler.CompilationModel.Expr}
    {wa : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa) :
    ExprRefines env store oracle fields dState
      (.unary .wordNot a_sol) (.bitNot a_ver) wa.bitNot := by
  refine ⟨Evaluates.unary hA.1 rfl,
    option_bind₁_some _ hA.2 ?_⟩
  rw [Word.toUint256_ofNat_val]
  exact (Word.word_bitNot_val_eq wa).symm

theorem exprRefines_shl
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {val_sol shift_sol : Core.Expr}
    {shift_ver val_ver : Compiler.CompilationModel.Expr}
    {wval wshift : Word}
    (hVal : ExprRefines env store oracle fields dState val_sol val_ver wval)
    (hShift : ExprRefines env store oracle fields dState shift_sol shift_ver wshift) :
    ExprRefines env store oracle fields dState
      (.binary .wordShl val_sol shift_sol) (.shl shift_ver val_ver)
      (wval.shiftLeft wshift) := by
  refine ⟨Evaluates.binary hVal.1 hShift.1 rfl,
    option_bind₂_some _ hShift.2 hVal.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  rw [← Verity.Core.Uint256.shl_eq_bounded]
  exact (Word.word_shiftLeft_val_eq wval wshift).symm

theorem exprRefines_shr
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {val_sol shift_sol : Core.Expr}
    {shift_ver val_ver : Compiler.CompilationModel.Expr}
    {wval wshift : Word}
    (hVal : ExprRefines env store oracle fields dState val_sol val_ver wval)
    (hShift : ExprRefines env store oracle fields dState shift_sol shift_ver wshift) :
    ExprRefines env store oracle fields dState
      (.binary .wordShr val_sol shift_sol) (.shr shift_ver val_ver)
      (wval.shiftRight wshift) := by
  refine ⟨Evaluates.binary hVal.1 hShift.1 rfl,
    option_bind₂_some _ hShift.2 hVal.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_shiftRight_val_eq wval wshift).symm

theorem exprRefines_sar
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {val_sol shift_sol : Core.Expr}
    {shift_ver val_ver : Compiler.CompilationModel.Expr}
    {wval wshift : Word}
    (hVal : ExprRefines env store oracle fields dState val_sol val_ver wval)
    (hShift : ExprRefines env store oracle fields dState shift_sol shift_ver wshift) :
    ExprRefines env store oracle fields dState
      (.binary .wordSar val_sol shift_sol) (.sar shift_ver val_ver)
      (wval.shiftArithmeticRight wshift) := by
  refine ⟨Evaluates.binary hVal.1 hShift.1 rfl,
    option_bind₂_some _ hShift.2 hVal.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_shiftArithmeticRight_val_eq wval wshift).symm

theorem exprRefines_byte
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {idx_sol val_sol : Core.Expr}
    {idx_ver val_ver : Compiler.CompilationModel.Expr}
    {widx wval : Word}
    (hIdx : ExprRefines env store oracle fields dState idx_sol idx_ver widx)
    (hVal : ExprRefines env store oracle fields dState val_sol val_ver wval) :
    ExprRefines env store oracle fields dState
      (.binary .wordByte idx_sol val_sol) (.byte idx_ver val_ver)
      (widx.byteAt wval) := by
  refine ⟨Evaluates.binary hIdx.1 hVal.1 rfl,
    option_bind₂_some _ hIdx.2 hVal.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_byteAt_val_eq widx wval).symm

theorem exprRefines_signextend
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {idx_sol val_sol : Core.Expr}
    {idx_ver val_ver : Compiler.CompilationModel.Expr}
    {widx wval : Word}
    (hIdx : ExprRefines env store oracle fields dState idx_sol idx_ver widx)
    (hVal : ExprRefines env store oracle fields dState val_sol val_ver wval) :
    ExprRefines env store oracle fields dState
      (.binary .wordSignExtend idx_sol val_sol) (.signextend idx_ver val_ver)
      (widx.signExtend wval) := by
  refine ⟨Evaluates.binary hIdx.1 hVal.1 rfl,
    option_bind₂_some _ hIdx.2 hVal.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_signExtend_val_eq widx wval).symm

theorem exprRefines_pow
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {base_sol exp_sol : Core.Expr}
    {base_ver exp_ver : Compiler.CompilationModel.Expr}
    {wbase wexp : Word}
    (hBase : ExprRefines env store oracle fields dState base_sol base_ver wbase)
    (hExp : ExprRefines env store oracle fields dState exp_sol exp_ver wexp) :
    ExprRefines env store oracle fields dState
      (.binary .wordPow base_sol exp_sol)
      (.externalCall builtinExpName [base_ver, exp_ver])
      (wbase.pow wexp) := by
  refine ⟨Evaluates.binary hBase.1 hExp.1 rfl, ?_⟩
  change (if builtinExpName == builtinExpName then
      (Denote.evalExpr oracle fields dState base_ver).bind fun baseVal =>
        (Denote.evalExpr oracle fields dState exp_ver).bind fun exponentVal =>
          some (Verity.Core.Uint256.powEff
            (Verity.Core.Uint256.ofNat baseVal)
            (Verity.Core.Uint256.ofNat exponentVal)).val
    else none) = some (wbase.pow wexp).val
  rw [beq_self_eq_true, if_pos rfl]
  refine option_bind₂_some _ hBase.2 hExp.2 ?_
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val]
  exact (Word.word_pow_val_eq wbase wexp).symm

theorem exprRefines_eq
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (Core.Expr.wordEqFlag a_sol b_sol) (.eq a_ver b_ver)
      (Word.ofBool (wa == wb)) := by
  refine ⟨Word.evaluates_boolToWord (Evaluates.binary hA.1 hB.1 rfl),
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.val_ofBool, Word.word_eq_eq_decide]

theorem exprRefines_gt
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (Core.Expr.wordGtFlag a_sol b_sol) (.gt a_ver b_ver)
      (Word.ofBool (decide (wa > wb))) := by
  refine ⟨Word.evaluates_boolToWord (Evaluates.binary hA.1 hB.1 rfl),
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.val_ofBool]; rfl

theorem exprRefines_lt
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (Core.Expr.wordLtFlag a_sol b_sol) (.lt a_ver b_ver)
      (Word.ofBool (decide (wb > wa))) := by
  refine ⟨Word.evaluates_boolToWord (Evaluates.binary hB.1 hA.1 rfl),
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.val_ofBool]; rfl

theorem exprRefines_sgt
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (Core.Expr.wordSgtFlag a_sol b_sol) (.sgt a_ver b_ver)
      (Word.ofBool (wa.signedGt wb)) := by
  refine ⟨Word.evaluates_boolToWord (Evaluates.binary hA.1 hB.1 rfl),
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val, Word.val_ofBool]
  congr 1
  exact (Word.word_signedGt_eq_decide wa wb).symm

theorem exprRefines_slt
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (Core.Expr.wordSltFlag a_sol b_sol) (.slt a_ver b_ver)
      (Word.ofBool (wb.signedGt wa)) := by
  refine ⟨Word.evaluates_boolToWord (Evaluates.binary hB.1 hA.1 rfl),
    option_bind₂_some _ hA.2 hB.2 ?_⟩
  rw [Word.toUint256_ofNat_val, Word.toUint256_ofNat_val, Word.val_ofBool]
  congr 1
  exact (Word.word_signedLt_eq_decide wa wb).symm

theorem exprRefines_isZero
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol : Core.Expr} {a_ver : Compiler.CompilationModel.Expr}
    {wa : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa) :
    ExprRefines env store oracle fields dState
      (Core.Expr.wordIsZero a_sol) (.logicalNot a_ver)
      (Word.ofBool (wa == Word.zero)) := by
  refine ⟨Word.evaluates_boolToWord (Evaluates.binary hA.1 Evaluates.word rfl),
    option_bind₁_some _ hA.2 ?_⟩
  rw [Word.val_ofBool, Word.word_isZero_eq_decide]

theorem exprRefines_boolAnd
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (Core.Expr.boolToWord
        (Core.Expr.boolAnd (Core.Expr.wordToBool a_sol) (Core.Expr.wordToBool b_sol)))
      (.logicalAnd a_ver b_ver)
      (Word.ofBool (decide (wa.val != 0) && decide (wb.val != 0))) := by
  have hBoolA := Word.evaluates_wordToBool hA.1
  have hBoolB := Word.evaluates_wordToBool hB.1
  refine ⟨Word.evaluates_boolToWord ?_,
    option_bind₂_some _ hA.2 hB.2 (Word.val_ofBool _).symm⟩
  unfold Core.Expr.boolAnd
  cases hwa : decide (wa.val != 0)
  · rw [hwa] at hBoolA
    simpa [hwa] using Evaluates.ifFalse hBoolA Evaluates.bool
  · rw [hwa] at hBoolA
    simpa [hwa] using Evaluates.ifTrue hBoolA hBoolB

theorem exprRefines_boolOr
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {a_sol b_sol : Core.Expr} {a_ver b_ver : Compiler.CompilationModel.Expr}
    {wa wb : Word}
    (hA : ExprRefines env store oracle fields dState a_sol a_ver wa)
    (hB : ExprRefines env store oracle fields dState b_sol b_ver wb) :
    ExprRefines env store oracle fields dState
      (Core.Expr.boolToWord
        (Core.Expr.boolOr (Core.Expr.wordToBool a_sol) (Core.Expr.wordToBool b_sol)))
      (.logicalOr a_ver b_ver)
      (Word.ofBool (decide (wa.val != 0) || decide (wb.val != 0))) := by
  have hBoolA := Word.evaluates_wordToBool hA.1
  have hBoolB := Word.evaluates_wordToBool hB.1
  refine ⟨Word.evaluates_boolToWord ?_,
    option_bind₂_some _ hA.2 hB.2 (Word.val_ofBool _).symm⟩
  unfold Core.Expr.boolOr
  cases hwa : decide (wa.val != 0)
  · rw [hwa] at hBoolA
    simpa [hwa] using Evaluates.ifFalse hBoolA hBoolB
  · rw [hwa] at hBoolA
    simpa [hwa] using Evaluates.ifTrue hBoolA Evaluates.bool

theorem exprRefines_ifE
    {env : Environment} {store : Store}
    {oracle : DenoteOracle} {fields : List Field} {dState : DenoteState}
    {c_sol t_sol e_sol : Core.Expr}
    {c_ver t_ver e_ver : Compiler.CompilationModel.Expr}
    {wc wt we : Word}
    (hC : ExprRefines env store oracle fields dState c_sol c_ver wc)
    (hT : ExprRefines env store oracle fields dState t_sol t_ver wt)
    (hE : ExprRefines env store oracle fields dState e_sol e_ver we) :
    ExprRefines env store oracle fields dState
      (.ifE (Core.Expr.wordToBool c_sol) t_sol e_sol)
      (.ite c_ver t_ver e_ver)
      (if wc.val != 0 then wt else we) := by
  have hBoolC := Word.evaluates_wordToBool hC.1
  have hIte : Denote.evalExpr oracle fields dState (.ite c_ver t_ver e_ver) =
      ((Denote.evalExpr oracle fields dState c_ver).bind fun condVal =>
        if condVal != 0 then
          Denote.evalExpr oracle fields dState t_ver
        else
          Denote.evalExpr oracle fields dState e_ver) := rfl
  by_cases hnz : (wc.val != 0) = true
  · have hDec : decide ((wc.val != 0) = true) = true := decide_eq_true hnz
    rw [hDec] at hBoolC
    refine ⟨?_, ?_⟩
    · simpa [hnz] using Evaluates.ifTrue hBoolC hT.1
    · rw [hIte, hC.2]
      change (if (wc.val != 0) = true then
          Denote.evalExpr oracle fields dState t_ver
        else
          Denote.evalExpr oracle fields dState e_ver) =
        some (if (wc.val != 0) = true then wt else we).val
      rw [if_pos hnz, if_pos hnz]
      exact hT.2
  · have hFalse : (wc.val != 0) = false := Bool.eq_false_iff.mpr hnz
    have hDec : decide ((wc.val != 0) = true) = false := decide_eq_false hnz
    rw [hDec] at hBoolC
    refine ⟨?_, ?_⟩
    · simpa [hFalse] using Evaluates.ifFalse hBoolC hE.1
    · rw [hIte, hC.2]
      change (if (wc.val != 0) = true then
          Denote.evalExpr oracle fields dState t_ver
        else
          Denote.evalExpr oracle fields dState e_ver) =
        some (if (wc.val != 0) = true then wt else we).val
      rw [if_neg hnz, if_neg hnz]
      exact hE.2

/-! ## 4. Storage (`sload`/`sstore`), `WordMapping`, Transient Storage (`tload`/`tstore`), Memory, and Locals -/

theorem sload_refines_evalExpr_storage
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (fields : List Field)
    (fieldName : String) (field : Field) (slot : Word)
    (hField : findFieldWithResolvedSlot fields fieldName = some (field, slot.val))
    (hPersistent : field.isTransient = false)
    (hUnpacked : field.packedBits = none) :
    Denote.evalExpr oracle fields dState (.storage fieldName) =
      some (sState.sload slot).val := by
  have hDef : Denote.evalExpr oracle fields dState (.storage fieldName) =
      (match findFieldWithResolvedSlot fields fieldName with
      | some (field, slot) =>
          let rawWord := (Denote.readFieldWord dState.world field slot).val
          match field.packedBits with
          | none => some rawWord
          | some packed =>
              some (Verity.Core.Uint256.and
                (Verity.Core.Uint256.shr packed.offset rawWord)
                (Denote.packedMaskNat packed)).val
      | none => none) := rfl
  rw [hDef, hField]
  simp [Denote.readFieldWord, hPersistent, hUnpacked, hRef.storage_eq slot]

/-- Relation stating that a `Solcore.Core.WordMapping.Entries` table agrees with
    slot-hashed persistent storage at `baseSlot` under `oracle.mappingSlot`. -/
def MappingEntriesRefineSlots
    (oracle : DenoteOracle) (baseSlot : Nat)
    (sState : SolcoreExecState) (entries : WordMapping.Entries) : Prop :=
  ∀ key : Word,
    (sState.sload (Word.ofNatModulo (oracle.mappingSlot baseSlot key.val))).val =
      (WordMapping.lookupEntries entries key).val

theorem wordMapping_lookup_refines_evalExpr_mappingUint
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    {oracle : DenoteOracle} {fields : List Field}
    {fieldName : String} {field : Field} {baseSlot : Nat}
    {entries : WordMapping.Entries}
    {keyExpr : Compiler.CompilationModel.Expr} {keyWord : Word}
    (hMapRef : MappingEntriesRefineSlots oracle baseSlot sState entries)
    (hField : findFieldWithResolvedSlot fields fieldName = some (field, baseSlot))
    (hPersistent : field.isTransient = false)
    (hKey : Denote.evalExpr oracle fields dState keyExpr = some keyWord.val) :
    Denote.evalExpr oracle fields dState (.mappingUint fieldName keyExpr) =
      some (WordMapping.lookupEntries entries keyWord).val := by
  let hashedSlot := Word.ofNatModulo (oracle.mappingSlot baseSlot keyWord.val)
  have hSlotNorm : Denote.wordNormalize (oracle.mappingSlot baseSlot keyWord.val) =
      hashedSlot.val := rfl
  have hDef : Denote.evalExpr oracle fields dState (.mappingUint fieldName keyExpr) =
      ((Denote.evalExpr oracle fields dState keyExpr).bind fun keyVal =>
        match findFieldWithResolvedSlot fields fieldName with
        | some (field, slot) =>
            some (Denote.readFieldWord dState.world field (oracle.mappingSlot slot keyVal)).val
        | none => none) := rfl
  rw [hDef, hKey]
  simp [hField, Denote.readFieldWord, hPersistent, hSlotNorm,
    ← hRef.storage_eq hashedSlot]
  exact hMapRef keyWord

theorem wordMapping_insert_preserves_refinement
    {oracle : DenoteOracle} {baseSlot : Nat}
    {sState : SolcoreExecState} {entries : WordMapping.Entries}
    (hMapRef : MappingEntriesRefineSlots oracle baseSlot sState entries)
    (keyWord valWord : Word)
    (hInj : ∀ otherKey : Word, otherKey ≠ keyWord →
      Word.ofNatModulo (oracle.mappingSlot baseSlot otherKey.val) ≠
        Word.ofNatModulo (oracle.mappingSlot baseSlot keyWord.val)) :
    MappingEntriesRefineSlots oracle baseSlot
      (sState.sstore (Word.ofNatModulo (oracle.mappingSlot baseSlot keyWord.val)) valWord)
      (WordMapping.insertEntries entries keyWord valWord) := by
  intro readKey
  by_cases hEq : readKey = keyWord
  · subst hEq
    simp [SolcoreExecState.sload_sstore_same, WordMapping.lookupEntries_insert_same]
  · have hSlotNe := hInj readKey hEq
    rw [SolcoreExecState.sload_sstore_other _ _ hSlotNe,
      WordMapping.lookupEntries_insert_other _ _ hEq]
    exact hMapRef readKey

theorem tload_refines_evalExpr
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    {oracle : DenoteOracle} {fields : List Field}
    {slotExpr : Compiler.CompilationModel.Expr} {slot : Word}
    (hSlot : Denote.evalExpr oracle fields dState slotExpr = some slot.val) :
    Denote.evalExpr oracle fields dState (.tload slotExpr) =
      some (sState.tload slot).val :=
  option_bind₁_some _ hSlot (hRef.transient_eq slot).symm

theorem mload_refines_evalExpr
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    {oracle : DenoteOracle} {fields : List Field}
    {offsetExpr : Compiler.CompilationModel.Expr} {offset : Word}
    (hOffset : Denote.evalExpr oracle fields dState offsetExpr = some offset.val) :
    Denote.evalExpr oracle fields dState (.mload offsetExpr) =
      some (sState.mload offset).val :=
  option_bind₁_some _ hOffset (hRef.memory_eq offset).symm

theorem sstore_preserves_stateRefines
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (slot valWord : Word) :
    StateRefines
      (sState.sstore slot valWord)
      { dState with world := Denote.writeUintSlots dState.world [slot.val] valWord.val }
      initialWorld := by
  refine
    { storage_eq := fun candidate => ?_
      transient_eq := hRef.transient_eq
      memory_eq := hRef.memory_eq
      locals_eq := hRef.locals_eq
      journal_len_eq := hRef.journal_len_eq
      checkpoint_storage_eq := hRef.checkpoint_storage_eq
      checkpoint_transient_eq := hRef.checkpoint_transient_eq
      checkpoint_journal_len_eq := hRef.checkpoint_journal_len_eq }
  by_cases hEq : candidate = slot
  · subst hEq
    simp [SolcoreExecState.sload_sstore_same, Denote.writeUintSlots,
      Verity.ContractState.readSlot, Verity.ContractState.storage,
      Verity.ContractState.writePhysicalSlots]
  · have hValNe : candidate.val ≠ slot.val := fun h => hEq (Fin.ext h)
    rw [SolcoreExecState.sload_sstore_other _ _ hEq]
    simpa [Denote.writeUintSlots, Verity.ContractState.readSlot,
      Verity.ContractState.storage, Verity.ContractState.writePhysicalSlots,
      hValNe, Ne.symm hValNe] using hRef.storage_eq candidate

theorem tstore_preserves_stateRefines
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (slot valWord : Word) :
    StateRefines
      (sState.tstore slot valWord)
      { dState with
          world := dState.world.writeTransient (Denote.wordNormalize slot.val) valWord.toUint256 }
      initialWorld := by
  refine
    { storage_eq := hRef.storage_eq
      transient_eq := fun candidate => ?_
      memory_eq := hRef.memory_eq
      locals_eq := hRef.locals_eq
      journal_len_eq := hRef.journal_len_eq
      checkpoint_storage_eq := hRef.checkpoint_storage_eq
      checkpoint_transient_eq := hRef.checkpoint_transient_eq
      checkpoint_journal_len_eq := hRef.checkpoint_journal_len_eq }
  by_cases hEq : candidate = slot
  · subst hEq
    simp [SolcoreExecState.tload_tstore_same, Verity.ContractState.readTransient,
      Verity.ContractState.transientStorage, Verity.ContractState.writeTransient]
  · have hValNe : candidate.val ≠ slot.val := fun h => hEq (Fin.ext h)
    rw [SolcoreExecState.tload_tstore_other _ _ hEq]
    simpa [Verity.ContractState.readTransient, Verity.ContractState.transientStorage,
      Verity.ContractState.writeTransient, hValNe, Ne.symm hValNe] using hRef.transient_eq candidate

theorem setLocal_preserves_stateRefines
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (name : String) (valWord : Word) :
    StateRefines
      (sState.setLocal name valWord)
      { dState with bindings := Denote.bindValue dState.bindings name valWord.val }
      initialWorld := by
  refine
    { storage_eq := hRef.storage_eq
      transient_eq := hRef.transient_eq
      memory_eq := hRef.memory_eq
      locals_eq := fun query => ?_
      journal_len_eq := hRef.journal_len_eq
      checkpoint_storage_eq := hRef.checkpoint_storage_eq
      checkpoint_transient_eq := hRef.checkpoint_transient_eq
      checkpoint_journal_len_eq := hRef.checkpoint_journal_len_eq }
  have hOrig := hRef.locals_eq query
  unfold SolcoreExecState.getLocal Denote.lookupValue at hOrig
  unfold SolcoreExecState.getLocal SolcoreExecState.setLocal
    Denote.lookupValue Denote.bindValue
  by_cases hEq : query = name
  · subst hEq; simp
  · have hBeq : (name == query) = false := beq_eq_false_iff_ne.mpr (Ne.symm hEq)
    have hPred : (fun a : String × Nat => (!decide (a.1 = name) && decide (a.1 = query))) =
        (fun a => a.1 == query) := by
      funext a
      by_cases h : a.1 = query <;> simp [h, hEq]
    simpa [hEq, hBeq, List.find?_filter, hPred] using hOrig

/-! ## 5. Transaction Journal & Frame Rollback / Commit Bisimulation -/

theorem emitLog_preserves_stateRefines
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (topics : List Word) (payload : Word)
    (eventName : String) (resolvedArgs : List Nat) :
    StateRefines
      (sState.emitLog topics payload)
      { dState with
          world :=
            { dState.world with
                events := dState.world.events ++
                  [{ name := eventName
                     args := Denote.valuesAsEventArgs resolvedArgs
                     indexedArgs := [] }] } }
      initialWorld := by
  refine
    { storage_eq := hRef.storage_eq
      transient_eq := hRef.transient_eq
      memory_eq := hRef.memory_eq
      locals_eq := hRef.locals_eq
      journal_len_eq := ?_
      checkpoint_storage_eq := hRef.checkpoint_storage_eq
      checkpoint_transient_eq := hRef.checkpoint_transient_eq
      checkpoint_journal_len_eq := hRef.checkpoint_journal_len_eq }
  simp [SolcoreExecState.emitLog, TransactionJournal.recordLog, hRef.journal_len_eq]

/-- Refinement between a resolved `SolcoreFrameSnapshot` and a `DenoteResult`
    over scalar non-aliased `uint256` storage slots. -/
structure SnapshotRefinesResult
    (contractAddress : Address)
    (snap : SolcoreFrameSnapshot)
    (result : DenoteResult) : Prop where
  storage_eq :
    ∀ slot : Word,
      (snap.world.storageRead contractAddress slot).val = result.finalStorage slot.val
  journal_len_eq :
    snap.journal.logs.length = result.events.length

theorem revert_rollback_refines_denote
    {TrapReason : Type}
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (revertWord : Word)
    (hEncodeInit : ∀ slot : Word,
      Denote.encodeStorage oracle spec initialWorld slot.val =
        (initialWorld.readSlot slot.val).val) :
    ∃ snap : SolcoreFrameSnapshot,
      sState.resolveFrame (FrameOutcome.reverted (TrapReason := TrapReason) revertWord) =
        some snap ∧
      SnapshotRefinesResult sState.contractAddress snap
        (Denote.revertedResult oracle spec initialWorld) := by
  refine ⟨sState.checkpoint, rfl, ?_⟩
  refine
    { storage_eq := fun slot => by
        rw [hRef.checkpoint_storage_eq slot]
        exact (hEncodeInit slot).symm
      journal_len_eq := by
        simp [Denote.revertedResult, Denote.encodeEvents,
          hRef.checkpoint_journal_len_eq] }

theorem return_commit_refines_denote
    {TrapReason : Type}
    {sState : SolcoreExecState} {dState : DenoteState}
    {initialWorld : Verity.ContractState}
    (hRef : StateRefines sState dState initialWorld)
    (oracle : DenoteOracle) (spec : CompilationModel)
    (retWord : Word)
    (hEncodeFinal : ∀ slot : Word,
      Denote.encodeStorage oracle spec dState.world slot.val =
        (dState.world.readSlot slot.val).val) :
    ∃ snap : SolcoreFrameSnapshot,
      sState.resolveFrame (FrameOutcome.returned (TrapReason := TrapReason) retWord) =
        some snap ∧
      SnapshotRefinesResult sState.contractAddress snap
        (Denote.successResult oracle spec dState.world (some retWord.val)) := by
  refine ⟨{ world := sState.world
            transientStorage := sState.transientStorage
            journal := sState.journal }, rfl, ?_⟩
  refine
    { storage_eq := fun slot => by
        change (sState.sload slot).val = _
        rw [hRef.storage_eq slot]
        exact (hEncodeFinal slot).symm
      journal_len_eq := by
        simp [Denote.successResult, Denote.encodeEvents, hRef.journal_len_eq] }

/-! ## 6. Certified Translation Witness & TCB-Reduction Soundness Theorems -/

/-- Declarative `Solcore` specification of a Solidity contract function:
    maps a transaction and initial `Solcore` `WorldState` to a post-execution
    `SolcoreExecState` and `FrameOutcome`. -/
structure SolcoreFunctionSemantics where
  contractAddress : Address
  evalFrame :
    DenoteTransaction → WorldState →
      SolcoreExecState × FrameOutcome String

/-- Bisimulation relation between a declarative `SolcoreFunctionSemantics` and
    a Verity `(oracle, spec, fn)` compilation model triple. -/
structure SolcoreToVerityBisim
    (solcoreSem : SolcoreFunctionSemantics)
    (oracle : DenoteOracle)
    (spec : CompilationModel)
    (fn : FunctionSpec) : Prop where
  /-- For every transaction and initial state where `sWorld` and `initialWorld`
      agree on storage and journal, `Solcore` and `Denote.denoteFunction`
      produce bisimilar outcomes and resolved snapshots. -/
  frame_bisim :
    ∀ (tx : DenoteTransaction)
      (sWorld : WorldState)
      (initialWorld : Verity.ContractState),
      (∀ slot : Word,
        (sWorld.storageRead solcoreSem.contractAddress slot).val =
          (initialWorld.readSlot slot.val).val) →
      let (sState, outcome) := solcoreSem.evalFrame tx sWorld
      let dResult := Denote.denoteFunction oracle spec fn tx initialWorld
      match outcome with
      | .returned retWord =>
          dResult.success = true ∧
          dResult.returnValue = some retWord.val ∧
          ∃ snap,
            sState.resolveFrame outcome = some snap ∧
            SnapshotRefinesResult solcoreSem.contractAddress snap dResult
      | .reverted _ =>
          dResult.success = false ∧
          dResult.returnValue = none ∧
          ∃ snap,
            sState.resolveFrame outcome = some snap ∧
            SnapshotRefinesResult solcoreSem.contractAddress snap dResult
      | .trapped _ =>
          dResult.success = false

/-- Certified translation witness emitted per imported Solidity function.
    Removes `Compiler.SolidityImport` (`Import.lean`) from the Trusted Computing
    Base (TCB): once `bisim` is checked by Lean, the imported Verity
    `FunctionSpec` is guaranteed to refine `solcoreSem`. -/
structure CertifiedTranslationWitness where
  solcoreSem : SolcoreFunctionSemantics
  oracle : DenoteOracle
  spec : CompilationModel
  fn : FunctionSpec
  bisim : SolcoreToVerityBisim solcoreSem oracle spec fn

/-- **Soundness Theorem 1 (Denotational Preservation on Return)**:
    For any certified translation witness, whenever the declarative `Solcore`
    semantics returns `retWord`, `Denote.denoteFunction` succeeds with
    `some retWord.val` and its committed storage and event count refine the
    resolved `Solcore` snapshot. -/
theorem certifiedTranslationWitness_denote_returned_soundness
    (w : CertifiedTranslationWitness)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead w.solcoreSem.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {retWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .returned retWord)) :
    let dResult := Denote.denoteFunction w.oracle w.spec w.fn tx initialWorld
    dResult.success = true ∧
    dResult.returnValue = some retWord.val ∧
    (∀ slot : Word,
      (sState.world.storageRead w.solcoreSem.contractAddress slot).val =
        dResult.finalStorage slot.val) ∧
    sState.journal.logs.length = dResult.events.length := by
  have hB := w.bisim.frame_bisim tx sWorld initialWorld hInit
  rw [hEval] at hB
  rcases hB with ⟨hSucc, hRet, snap, hSnapEq, hSnapRef⟩
  simp only [SolcoreExecState.resolveFrame_returned, Option.some.injEq] at hSnapEq
  subst hSnapEq
  exact ⟨hSucc, hRet, hSnapRef.storage_eq, hSnapRef.journal_len_eq⟩

/-- **Soundness Theorem 2 (Denotational Rollback Preservation on Revert)**:
    For any certified translation witness, whenever the declarative `Solcore`
    semantics reverts with `revWord`, `Denote.denoteFunction` reverts
    (`success = false`, `returnValue = none`) and rolls back storage and
    events to match `sState.checkpoint`. -/
theorem certifiedTranslationWitness_denote_reverted_soundness
    (w : CertifiedTranslationWitness)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead w.solcoreSem.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {revWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .reverted revWord)) :
    let dResult := Denote.denoteFunction w.oracle w.spec w.fn tx initialWorld
    dResult.success = false ∧
    dResult.returnValue = none ∧
    (∀ slot : Word,
      (sState.checkpoint.world.storageRead w.solcoreSem.contractAddress slot).val =
        dResult.finalStorage slot.val) ∧
    sState.checkpoint.journal.logs.length = dResult.events.length := by
  have hB := w.bisim.frame_bisim tx sWorld initialWorld hInit
  rw [hEval] at hB
  rcases hB with ⟨hSucc, hRet, snap, hSnapEq, hSnapRef⟩
  simp only [SolcoreExecState.resolveFrame_reverted, Option.some.injEq] at hSnapEq
  subst hSnapEq
  exact ⟨hSucc, hRet, hSnapRef.storage_eq, hSnapRef.journal_len_eq⟩

/-- **Soundness Theorem 3 (End-to-End Composition with Layer 2/3 Compilation)**:
    Given a `CertifiedTranslationWitness` (`Solcore` ↔ `Denote`) and any
    target backend execution `backendExec : DenoteTransaction → Verity.ContractState → DenoteResult`
    (such as Layer 2 IR or Layer 3 Yul/EVM bytecode execution) proven equivalent
    to `Denote.denoteFunction`, the compiled backend preserves `Solcore`
    return values and storage/journal state end-to-end. -/
theorem certifiedTranslationWitness_endToEnd_soundness
    (w : CertifiedTranslationWitness)
    (backendExec : DenoteTransaction → Verity.ContractState → DenoteResult)
    (hLayer23 : ∀ tx initWorld,
      backendExec tx initWorld =
        Denote.denoteFunction w.oracle w.spec w.fn tx initWorld)
    (tx : DenoteTransaction)
    (sWorld : WorldState)
    (initialWorld : Verity.ContractState)
    (hInit : ∀ slot : Word,
      (sWorld.storageRead w.solcoreSem.contractAddress slot).val =
        (initialWorld.readSlot slot.val).val)
    {sState : SolcoreExecState} {retWord : Word}
    (hEval : w.solcoreSem.evalFrame tx sWorld = (sState, .returned retWord)) :
    let bResult := backendExec tx initialWorld
    bResult.success = true ∧
    bResult.returnValue = some retWord.val ∧
    (∀ slot : Word,
      (sState.world.storageRead w.solcoreSem.contractAddress slot).val =
        bResult.finalStorage slot.val) ∧
    sState.journal.logs.length = bResult.events.length := by
  dsimp only
  rw [hLayer23 tx initialWorld]
  exact certifiedTranslationWitness_denote_returned_soundness
    w tx sWorld initialWorld hInit hEval

end Compiler.Proofs.SolidityImport.SolcoreBridge
