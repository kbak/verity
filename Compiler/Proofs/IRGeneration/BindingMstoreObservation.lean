import Compiler.Proofs.IRGeneration.BindingMstoreExecution
import Compiler.Proofs.IRGeneration.BoundedMstoreObservation

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel
open Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.PhysicalMemory
open SourceSemantics

/-- Equal post-block word observations follow from actual successful canonical executions. -/
theorem mload_eq_of_exec_binding_mstore_block (spec : CompilationModel) (fields : List Field)
    (left right nextLeft nextRight : RuntimeState)
    (stmts : List Stmt) (writes : List (Nat × Verity.Core.Uint256)) (offset : Nat)
    (block : BindingMstoreBlock left.bindings stmts writes)
    (sameBindings : MstoreBlockBindingsAgree left.bindings right.bindings stmts)
    (leftCoherent : Coherent left.world) (rightCoherent : Coherent right.world)
    (readBound : offset + 32 ≤ Compiler.Constants.evmModulus)
    (same : ∀ query, offset ≤ query → query < offset + 32 →
      (∀ write ∈ writes, query < write.1 ∨ write.1 + 32 ≤ query) →
      left.world.physicalByte query = right.world.physicalByte query)
    (leftRun : execStmtsCanonical spec fields left stmts =
      .continue nextLeft)
    (rightRun : execStmtsCanonical spec fields right stmts =
      .continue nextRight) :
    evalExprCanonical spec fields nextLeft (.mload (.literal offset)) =
      evalExprCanonical spec fields nextRight (.mload (.literal offset)) := by
  have rightBlock : BindingMstoreBlock right.bindings stmts writes :=
    binding_mstore_block_of_bindings_agree block sameBindings
  exact mload_eq_of_exec_bounded_mstore_block spec fields left right nextLeft nextRight
    writes offset (binding_mstore_block_bounded block) leftCoherent rightCoherent readBound same
    ((exec_binding_mstore_block_eq_literal spec fields left stmts writes block).symm.trans leftRun)
    ((exec_binding_mstore_block_eq_literal spec fields right stmts writes rightBlock).symm.trans
      rightRun)

/-- Execute the common store block before comparing its bounded canonical hash observations. -/
theorem keccak_eq_of_exec_binding_mstore_block (spec : CompilationModel) (fields : List Field)
    (left right nextLeft nextRight : RuntimeState)
    (stmts : List Stmt) (writes : List (Nat × Verity.Core.Uint256)) (offset size : Nat)
    (block : BindingMstoreBlock left.bindings stmts writes)
    (sameBindings : MstoreBlockBindingsAgree left.bindings right.bindings stmts)
    (leftCoherent : Coherent left.world) (rightCoherent : Coherent right.world)
    (offsetBound : offset < Compiler.Constants.evmModulus)
    (sizeBound : size < Compiler.Constants.evmModulus)
    (readBound : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (same : ∀ query, offset ≤ query → query < offset + size →
      (∀ write ∈ writes, query < write.1 ∨ write.1 + 32 ≤ query) →
      left.world.physicalByte query = right.world.physicalByte query)
    (leftRun : execStmtsCanonical spec fields left stmts =
      .continue nextLeft)
    (rightRun : execStmtsCanonical spec fields right stmts =
      .continue nextRight) :
    evalExprCanonical spec fields nextLeft (.keccak256 (.literal offset) (.literal size)) =
      evalExprCanonical spec fields nextRight (.keccak256 (.literal offset) (.literal size)) := by
  have rightBlock : BindingMstoreBlock right.bindings stmts writes :=
    binding_mstore_block_of_bindings_agree block sameBindings
  exact keccak_eq_of_exec_bounded_mstore_block spec fields left right nextLeft nextRight
    writes offset size (binding_mstore_block_bounded block) leftCoherent rightCoherent
    offsetBound sizeBound readBound same
    ((exec_binding_mstore_block_eq_literal spec fields left stmts writes block).symm.trans leftRun)
    ((exec_binding_mstore_block_eq_literal spec fields right stmts writes rightBlock).symm.trans
      rightRun)

end Compiler.Proofs.IRGeneration
