import Compiler.Proofs.IRGeneration.BoundedMstoreExecution
import Compiler.Proofs.IRGeneration.CallerMemoryComposition

/-! Word and hash observations after actual canonical literal-store execution.
This composes the execution bridge with existing two-run memory observations;
it does not establish compiler correspondence or analyze dynamic caller operands. -/

namespace Compiler.Proofs.IRGeneration
open Compiler.CompilationModel
open Compiler.CompilationModel.DenoteMemory
open Compiler.CompilationModel.PhysicalMemory
open SourceSemantics

/-- A bounded literal load reads the canonical runtime's physical word observation. -/
theorem eval_canonical_literal_mload (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (offset : Nat) (bounded : offset < Compiler.Constants.evmModulus) :
    evalExprCanonical spec fields state (.mload (.literal offset)) =
      some (state.world.memory offset).val := by
  have resolved := eval_canonical_literal_of_lt spec fields state offset bounded
  unfold evalExprCanonical at resolved ⊢
  rw [evalExprWithHelpers.eq_def]
  simp only [resolved]
  rfl

/-- Bounded hash literals select their original offset and size without truncation. -/
theorem eval_canonical_literal_keccak (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (offset size : Nat)
    (offsetBound : offset < Compiler.Constants.evmModulus)
    (sizeBound : size < Compiler.Constants.evmModulus) :
    evalExprCanonical spec fields state (.keccak256 (.literal offset) (.literal size)) =
      some (abstractKeccakMemorySlice (fun address => (state.world.memory address).val)
        offset size) := by
  have hOffset := eval_canonical_literal_of_lt spec fields state offset offsetBound
  have hSize := eval_canonical_literal_of_lt spec fields state size sizeBound
  unfold evalExprCanonical at hOffset hSize ⊢
  rw [evalExprWithHelpers.eq_def]
  simp only [hOffset, hSize, keccakMemorySlice]
  rfl

/-- Equal post-block word observations follow from actual successful canonical executions. -/
theorem mload_eq_of_exec_bounded_mstore_block (spec : CompilationModel) (fields : List Field)
    (left right nextLeft nextRight : RuntimeState)
    (writes : List (Nat × Verity.Core.Uint256)) (offset : Nat)
    (bounded : BoundedMstoreWrites writes)
    (leftCoherent : Coherent left.world) (rightCoherent : Coherent right.world)
    (readBound : offset + 32 ≤ Compiler.Constants.evmModulus)
    (same : ∀ query, offset ≤ query → query < offset + 32 →
      (∀ write ∈ writes, query < write.1 ∨ write.1 + 32 ≤ query) →
      left.world.physicalByte query = right.world.physicalByte query)
    (leftRun : execStmtsCanonical spec fields left (literalMstoreBlock writes) =
      .continue nextLeft)
    (rightRun : execStmtsCanonical spec fields right (literalMstoreBlock writes) =
      .continue nextRight) :
    evalExprCanonical spec fields nextLeft (.mload (.literal offset)) =
      evalExprCanonical spec fields nextRight (.mload (.literal offset)) := by
  rw [mstore_block_state_eq_of_exec spec fields left nextLeft writes bounded leftRun,
    mstore_block_state_eq_of_exec spec fields right nextRight writes bounded rightRun,
    eval_canonical_literal_mload spec fields _ offset (by omega),
    eval_canonical_literal_mload spec fields _ offset (by omega)]
  exact congrArg (fun word : Verity.Core.Uint256 => some word.val)
    (memory_writes_word_eq_of_eq_outside left.world right.world leftCoherent rightCoherent
      writes offset same)

/-- Execute the common store block before comparing its bounded canonical hash observations. -/
theorem keccak_eq_of_exec_bounded_mstore_block (spec : CompilationModel) (fields : List Field)
    (left right nextLeft nextRight : RuntimeState)
    (writes : List (Nat × Verity.Core.Uint256)) (offset size : Nat)
    (bounded : BoundedMstoreWrites writes)
    (leftCoherent : Coherent left.world) (rightCoherent : Coherent right.world)
    (offsetBound : offset < Compiler.Constants.evmModulus)
    (sizeBound : size < Compiler.Constants.evmModulus)
    (readBound : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (same : ∀ query, offset ≤ query → query < offset + size →
      (∀ write ∈ writes, query < write.1 ∨ write.1 + 32 ≤ query) →
      left.world.physicalByte query = right.world.physicalByte query)
    (leftRun : execStmtsCanonical spec fields left (literalMstoreBlock writes) =
      .continue nextLeft)
    (rightRun : execStmtsCanonical spec fields right (literalMstoreBlock writes) =
      .continue nextRight) :
    evalExprCanonical spec fields nextLeft (.keccak256 (.literal offset) (.literal size)) =
      evalExprCanonical spec fields nextRight (.keccak256 (.literal offset) (.literal size)) := by
  rw [mstore_block_state_eq_of_exec spec fields left nextLeft writes bounded leftRun,
    mstore_block_state_eq_of_exec spec fields right nextRight writes bounded rightRun,
    eval_canonical_literal_keccak spec fields _ offset size offsetBound sizeBound,
    eval_canonical_literal_keccak spec fields _ offset size offsetBound sizeBound]
  exact congrArg some (memory_writes_hash_eq_of_eq_outside left.world right.world
    leftCoherent rightCoherent writes offset size readBound same)

end Compiler.Proofs.IRGeneration
