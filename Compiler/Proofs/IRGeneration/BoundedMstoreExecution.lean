import Compiler.Proofs.IRGeneration.SourceSemantics
import Verity.Core.Model.MemoryComposition

/-! Canonical execution of bounded literal word-store blocks.
The proof utility constructs only literal `mstore` statements and identifies
all runtime fields of their successful poststate. It changes no admission rule. -/

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel
open Compiler.CompilationModel.DenoteMemory
open SourceSemantics

/-- A straight-line block whose addresses and word values are literal operands. -/
def literalMstoreBlock (writes : List (Nat × Verity.Core.Uint256)) : List Stmt :=
  writes.map fun write => .mstore (.literal write.1) (.literal write.2.val)

/-- Every full word footprint fits in the nonwrapping EVM address range. -/
def BoundedMstoreWrites (writes : List (Nat × Verity.Core.Uint256)) : Prop :=
  ∀ write ∈ writes, write.1 + 32 ≤ Compiler.Constants.evmModulus

/-- The exact runtime poststate specified by the existing physical write fold. -/
def mstoreBlockState (state : RuntimeState) (writes : List (Nat × Verity.Core.Uint256)) :
    RuntimeState :=
  { state with world := (writes.foldl
      (fun world write => world.writePhysicalMemoryValue write.1 write.2) state.world) }

/-- A bounded literal is evaluated without modular truncation. -/
theorem eval_canonical_literal_of_lt (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (number : Nat) (bounded : number < Compiler.Constants.evmModulus) :
    evalExprCanonical spec fields state (.literal number) = some number := by
  rw [evalExprCanonical_lit, wordNormalize_eq_mod, Nat.mod_eq_of_lt bounded]

/-- Expose one canonical store after both operands have successfully evaluated. -/
theorem exec_canonical_mstore_of_eval (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (offset word : Expr) (address data : Nat)
    (hOffset : evalExprCanonical spec fields state offset = some address)
    (hWord : evalExprCanonical spec fields state word = some data) :
    execStmtCanonical spec fields state (.mstore offset word) =
      .continue { state with world := (state.world.writePhysicalMemoryValue address
        (Verity.Core.Uint256.ofNat data)) } := by
  unfold execStmtCanonical
  unfold evalExprCanonical at hOffset hWord
  rw [execStmtWithHelpers.eq_def]
  simp only [hOffset, hWord]

/-- A bounded literal store writes the original typed word at the original address. -/
theorem exec_canonical_literal_mstore (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (offset : Nat) (word : Verity.Core.Uint256)
    (bounded : offset + 32 ≤ Compiler.Constants.evmModulus) :
    execStmtCanonical spec fields state (.mstore (.literal offset) (.literal word.val)) =
      .continue { state with world := state.world.writePhysicalMemoryValue offset word } := by
  have normalized : Verity.Core.Uint256.ofNat word.val = word := by
    apply Verity.Core.Uint256.ext
    exact Nat.mod_eq_of_lt word.isLt
  simpa only [normalized] using exec_canonical_mstore_of_eval spec fields state
    (.literal offset) (.literal word.val) offset word.val
    (eval_canonical_literal_of_lt spec fields state offset (by omega))
    (eval_canonical_literal_of_lt spec fields state word.val word.isLt)

/-- A canonical continuing head hands its exact poststate to the remaining block. -/
theorem exec_canonical_cons_of_continue (spec : CompilationModel) (fields : List Field)
    (state next : RuntimeState) (stmt : Stmt) (rest : List Stmt)
    (run : execStmtCanonical spec fields state stmt = .continue next) :
    execStmtsCanonical spec fields state (stmt :: rest) =
      execStmtsCanonical spec fields next rest := by
  unfold execStmtsCanonical
  unfold execStmtCanonical at run
  rw [execStmtListWithHelpers.eq_def]
  simp only [run]

/-- The whole bounded literal block executes to the physical write fold, in order. -/
theorem exec_bounded_literal_mstore_block (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (writes : List (Nat × Verity.Core.Uint256))
    (bounded : BoundedMstoreWrites writes) :
    execStmtsCanonical spec fields state (literalMstoreBlock writes) =
      .continue (mstoreBlockState state writes) := by
  induction writes generalizing state with
  | nil => exact execStmtsCanonical_nil spec fields state
  | cons write writes ih =>
      have head : write.1 + 32 ≤ Compiler.Constants.evmModulus :=
        bounded write List.mem_cons_self
      have tail : BoundedMstoreWrites writes :=
        fun item member => bounded item (List.mem_cons_of_mem write member)
      change execStmtsCanonical spec fields state
        (.mstore (.literal write.1) (.literal write.2.val) :: literalMstoreBlock writes) = _
      rw [exec_canonical_cons_of_continue spec fields state _ _ _
        (exec_canonical_literal_mstore spec fields state write.1 write.2 head), ih _ tail]
      rfl

/-- Recover the exact poststate from an observed successful canonical block execution. -/
theorem mstore_block_state_eq_of_exec (spec : CompilationModel) (fields : List Field)
    (state next : RuntimeState) (writes : List (Nat × Verity.Core.Uint256))
    (bounded : BoundedMstoreWrites writes)
    (run : execStmtsCanonical spec fields state (literalMstoreBlock writes) = .continue next) :
    next = mstoreBlockState state writes := by
  rw [exec_bounded_literal_mstore_block spec fields state writes bounded] at run
  exact (StmtResult.continue.inj run).symm

/-- Block execution preserves bindings and every other field after erasing both memory views. -/
theorem exec_bounded_literal_mstore_block_frame (spec : CompilationModel) (fields : List Field)
    (state next : RuntimeState) (writes : List (Nat × Verity.Core.Uint256))
    (bounded : BoundedMstoreWrites writes)
    (run : execStmtsCanonical spec fields state (literalMstoreBlock writes) = .continue next) :
    { next with world := next.world.installPhysicalMemory Memory.empty } =
      { state with world := state.world.installPhysicalMemory Memory.empty } := by
  rw [mstore_block_state_eq_of_exec spec fields state next writes bounded run]
  dsimp only [mstoreBlockState]
  rw [memory_writes_frame]

end Compiler.Proofs.IRGeneration
