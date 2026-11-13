import Compiler.Proofs.IRGeneration.BindingMstoreOperands

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel SourceSemantics
open Compiler.CompilationModel.DenoteMemory

/-- A store-only block with bound scalar operands and nonwrapping word footprints.
The witness records the resolved writes; it is not an importer admission rule. -/
inductive BindingMstoreBlock (bindings : List (String × Nat)) :
    List Stmt → List (Nat × Verity.Core.Uint256) → Prop where
  | nil : BindingMstoreBlock bindings [] []
  | cons {offset word : Expr} {address data : Nat} {rest : List Stmt}
      {writes : List (Nat × Verity.Core.Uint256)}
      (offsetOperand : BindingMstoreOperand bindings offset address)
      (wordOperand : BindingMstoreOperand bindings word data)
      (bounded : address + 32 ≤ Compiler.Constants.evmModulus)
      (tail : BindingMstoreBlock bindings rest writes) :
      BindingMstoreBlock bindings (.mstore offset word :: rest)
        ((address, Verity.Core.Uint256.ofNat data) :: writes)

/-- Two runtimes need agree only on bindings referenced by the block's store operands. -/
def MstoreBlockBindingsAgree (left right : List (String × Nat)) (stmts : List Stmt) : Prop :=
  ∀ offset word, .mstore offset word ∈ stmts →
    MstoreOperandBindingsAgree left right offset ∧ MstoreOperandBindingsAgree left right word

/-- The resolved write list inherits the block's complete word-footprint bounds. -/
theorem binding_mstore_block_bounded {bindings : List (String × Nat)} {stmts : List Stmt}
    {writes : List (Nat × Verity.Core.Uint256)} (block : BindingMstoreBlock bindings stmts writes) :
    BoundedMstoreWrites writes := by
  induction block with
  | nil => intro write member; cases member
  | @cons offset word address data rest writes hOffset hWord bounded tail ih =>
      intro write member
      rcases List.mem_cons.mp member with rfl | member
      · exact bounded
      · exact ih write member

/-- Binding agreement derives the same resolved write list in the second runtime. -/
theorem binding_mstore_block_of_bindings_agree {left right : List (String × Nat)}
    {stmts : List Stmt} {writes : List (Nat × Verity.Core.Uint256)}
    (block : BindingMstoreBlock left stmts writes)
    (same : MstoreBlockBindingsAgree left right stmts) :
    BindingMstoreBlock right stmts writes := by
  induction block with
  | nil => exact .nil
  | @cons offset word address data rest writes hOffset hWord bounded tail ih =>
      have head : MstoreOperandBindingsAgree left right offset ∧
          MstoreOperandBindingsAgree left right word := same offset word List.mem_cons_self
      refine .cons (binding_mstore_operand_of_bindings_agree hOffset head.1)
        (binding_mstore_operand_of_bindings_agree hWord head.2) bounded (ih ?_)
      intro nextOffset nextWord member
      exact same nextOffset nextWord (List.mem_cons_of_mem _ member)

/-- Canonical execution realizes the resolved write list and preserves the runtime frame. -/
theorem exec_binding_mstore_block (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (stmts : List Stmt) (writes : List (Nat × Verity.Core.Uint256))
    (block : BindingMstoreBlock state.bindings stmts writes) :
    execStmtsCanonical spec fields state stmts = .continue (mstoreBlockState state writes) := by
  generalize hBindings : state.bindings = bindings at block
  induction block generalizing state with
  | nil => exact execStmtsCanonical_nil spec fields state
  | @cons offset word address data rest writes hOffset hWord bounded tail ih =>
      have offsetEval : evalExprCanonical spec fields state offset = some address :=
        eval_canonical_binding_mstore_operand spec fields state offset address
          (hBindings.symm ▸ hOffset)
      have wordEval : evalExprCanonical spec fields state word = some data :=
        eval_canonical_binding_mstore_operand spec fields state word data (hBindings.symm ▸ hWord)
      rw [exec_canonical_cons_of_continue spec fields state _ _ _
        (exec_canonical_mstore_of_eval spec fields state offset word address data
          offsetEval wordEval)]
      rw [ih { state with world := (state.world.writePhysicalMemoryValue address
        (Verity.Core.Uint256.ofNat data)) } hBindings]
      rfl

/-- A witnessed block has exactly the result of its resolved literal-store block. -/
theorem exec_binding_mstore_block_eq_literal (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (stmts : List Stmt) (writes : List (Nat × Verity.Core.Uint256))
    (block : BindingMstoreBlock state.bindings stmts writes) :
    execStmtsCanonical spec fields state stmts =
      execStmtsCanonical spec fields state (literalMstoreBlock writes) := by
  rw [exec_binding_mstore_block spec fields state stmts writes block,
    exec_bounded_literal_mstore_block spec fields state writes (binding_mstore_block_bounded block)]

/-- Successful execution preserves every runtime field after erasing both memory views. -/
theorem exec_binding_mstore_block_frame (spec : CompilationModel) (fields : List Field)
    (state next : RuntimeState) (stmts : List Stmt) (writes : List (Nat × Verity.Core.Uint256))
    (block : BindingMstoreBlock state.bindings stmts writes)
    (run : execStmtsCanonical spec fields state stmts = .continue next) :
    { next with world := next.world.installPhysicalMemory Memory.empty } =
      { state with world := state.world.installPhysicalMemory Memory.empty } := by
  rw [exec_binding_mstore_block_eq_literal spec fields state stmts writes block] at run
  exact exec_bounded_literal_mstore_block_frame spec fields state next writes
    (binding_mstore_block_bounded block) run

end Compiler.Proofs.IRGeneration
