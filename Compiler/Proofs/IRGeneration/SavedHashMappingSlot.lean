import Compiler.Proofs.IRGeneration.SavedHashReturn
import Compiler.Proofs.IRGeneration.ScratchMemoryComposition

/-! Canonical execution of saved-hash capture, cleanup and mapping scratch.
The final local holds the Solidity slot derived from the physical bytes at capture. -/

namespace Compiler.Proofs.IRGeneration
open Compiler Compiler.CompilationModel SourceSemantics
open Compiler.CompilationModel.DenoteMemory Compiler.CompilationModel.PhysicalMemory

private theorem fold_be_eq_reverse_bytes (bytes : ByteArray) (i : Nat) (acc : List UInt8) :
    ByteArray.foldlM.loop (m := Id) (fun n b => pure (n * 256 + b.toNat)) bytes bytes.size
        (Nat.le_refl _) (bytes.size - i) i (EvmYul.fromBytes' acc) =
      EvmYul.fromBytes' (ByteArray.toList.loop bytes i acc).reverse := by
  induction i, acc using ByteArray.toList.loop.induct bytes with
  | case1 i acc hi ih =>
    have count : bytes.size - i = (bytes.size - (i + 1)) + 1 := by omega
    have byte : bytes.get! i = bytes[i] := getElem!_pos bytes.data i hi
    rw [count, ByteArray.foldlM.loop.eq_1, dif_pos hi, ByteArray.toList.loop, if_pos hi]
    simpa only [pure_bind, EvmYul.fromBytes', byte, UInt8.toFin_val, Nat.reducePow,
      Nat.add_comm, Nat.mul_comm] using ih
  | case2 i acc hi =>
    rw [ByteArray.foldlM.loop.eq_1, dif_neg hi, ByteArray.toList.loop, if_neg hi,
      List.reverse_reverse]
    rfl

/-- Both big-endian readers interpret the same digest bytes as the same natural number. -/
theorem byte_array_to_nat_be_eq_from_byte_array_big_endian (bytes : ByteArray) :
    KeccakEngine.byteArrayToNatBE bytes = EvmYul.fromByteArrayBigEndian bytes := by
  simpa only [KeccakEngine.byteArrayToNatBE, ByteArray.foldl, ByteArray.foldlM, Id.run,
    dif_pos (Nat.le_refl bytes.size), Nat.sub_zero, EvmYul.fromByteArrayBigEndian,
    EvmYul.fromBytesBigEndian, Function.comp_apply, ByteArray.toList, EvmYul.fromBytes'] using
    congrArg Id.run (fold_be_eq_reverse_bytes bytes 0 [])

/-- Hashing the ordered key and layout-base words yields the Solidity storage address. -/
theorem keccak_bytes_word_mapping_slot (key baseSlot : Verity.Core.Uint256) :
    (keccakBytesWord (Compiler.Proofs.abiEncodeMappingSlot baseSlot.val key.val)).val =
      Compiler.Proofs.solidityMappingSlot baseSlot.val key.val := by
  unfold keccakBytesWord
  rw [Verity.Core.Uint256.val_ofNat, byte_array_to_nat_be_eq_from_byte_array_big_endian]
  exact Nat.mod_eq_of_lt (Compiler.Proofs.solidityMappingSlot_lt_evmModulus _ _)

private theorem exec_mapping_scratch_stores (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (keyExpr baseExpr : Expr) (key baseSlot : Verity.Core.Uint256)
    (hKey : BindingMstoreOperand state.bindings keyExpr key.val)
    (hBase : BindingMstoreOperand state.bindings baseExpr baseSlot.val) :
    execStmtsCanonical spec fields state
        [.mstore (.literal 0) keyExpr, .mstore (.literal 32) baseExpr] =
      .continue { state with world := writeWordPair state.world 0 key baseSlot } := by
  have norm (w : Verity.Core.Uint256) : Verity.Core.Uint256.ofNat w.val = w :=
    Verity.Core.Uint256.ext (Nat.mod_eq_of_lt w.isLt)
  have stores := BindingMstoreBlock.cons (.literal 0 (by decide)) hKey (by decide)
    (.cons (.literal 32 (by decide)) hBase (by decide) .nil)
  simpa only [norm, mstoreBlockState, List.foldl_cons, List.foldl_nil, writeWordPair] using
    exec_binding_mstore_block spec fields state _ _ stores

private theorem exec_singleton_let_var_of_eval (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (name : String) (expr : Expr) (word : Nat)
    (evaluated : evalExprCanonical spec fields state expr = some word) :
    execStmtsCanonical spec fields state [.letVar name expr] =
      .continue { state with bindings := bindValue state.bindings name word } := by
  have step : execStmtCanonical spec fields state (.letVar name expr) =
      .continue { state with bindings := bindValue state.bindings name word } := by
    unfold evalExprCanonical at evaluated
    simp only [execStmtCanonical, execStmtWithHelpers.eq_def, evaluated]
  rw [exec_canonical_cons_of_continue _ _ _ _ _ _ step, execStmtsCanonical_nil]

/-- Execute the ordered scratch stores and bind the mapping address in the caller's local. -/
theorem exec_mapping_scratch (spec : CompilationModel) (fields : List Field) (state : RuntimeState)
    (keyExpr baseExpr : Expr) (key baseSlot : Verity.Core.Uint256) (result : String)
    (hKey : BindingMstoreOperand state.bindings keyExpr key.val)
    (hBase : BindingMstoreOperand state.bindings baseExpr baseSlot.val) :
    execStmtsCanonical spec fields state [.mstore (.literal 0) keyExpr,
        .mstore (.literal 32) baseExpr, .letVar result (.keccak256 (.literal 0) (.literal 64))] =
      .continue { state with
        world := writeWordPair state.world 0 key baseSlot
        bindings := bindValue state.bindings result
          (Compiler.Proofs.solidityMappingSlot baseSlot.val key.val) } := by
  let scratch := { state with world := writeWordPair state.world 0 key baseSlot }
  have digest := eval_canonical_keccak_of_physical_slice spec fields scratch
    (.literal 0) (.literal 64) 0 64 _
    (eval_canonical_literal_of_lt _ _ _ _ (by decide))
    (eval_canonical_literal_of_lt _ _ _ _ (by decide))
    (write_word_pair_coherent _ _ _ _) (by decide) (write_word_pair_mapping_preimage _ _ _ _)
  rw [keccak_bytes_word_mapping_slot] at digest
  exact (exec_canonical_append_of_continue spec fields state scratch
    [.mstore (.literal 0) keyExpr, .mstore (.literal 32) baseExpr]
    [.letVar result (.keccak256 (.literal 0) (.literal 64))]
    (exec_mapping_scratch_stores spec fields state keyExpr baseExpr key baseSlot hKey hBase)).trans
    (exec_singleton_let_var_of_eval spec fields scratch result _ _ digest)

/-- After cleanup, a lookup through the saved hash selects the mapping slot for the original
physical preimage. The cleanup may overwrite any part of that preimage. -/
theorem exec_saved_hash_mapping_slot (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (name result : String) (base length layout : Expr) (offset size : Nat)
    (bytes : ByteArray) (baseSlot : Verity.Core.Uint256)
    (cleanup : List Stmt) (writes : List (Nat × Verity.Core.Uint256))
    (hBase : evalExprCanonical spec fields state base = some offset)
    (hLength : evalExprCanonical spec fields state length = some size)
    (coherent : Coherent state.world)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (preimage : state.world.byteMemory.sliceBytes offset size = bytes)
    (block : BindingMstoreBlock (bindValue state.bindings name (keccakBytesWord bytes).val)
      cleanup writes)
    (hLayout : BindingMstoreOperand (bindValue state.bindings name (keccakBytesWord bytes).val)
      layout baseSlot.val) :
    let key := keccakBytesWord bytes
    let saved := { state with bindings := bindValue state.bindings name key.val }
    let cleaned := mstoreBlockState saved writes
    execStmtsCanonical spec fields state (.assignVar name (.keccak256 base length) ::
      (cleanup ++ [.mstore (.literal 0) (.localVar name), .mstore (.literal 32) layout,
        .letVar result (.keccak256 (.literal 0) (.literal 64))])) =
      .continue { cleaned with
        world := writeWordPair cleaned.world 0 key baseSlot
        bindings := bindValue cleaned.bindings result
          (Compiler.Proofs.solidityMappingSlot baseSlot.val key.val) } := by
  dsimp only
  rw [exec_saved_hash_cleanup_then spec fields state name base length offset size bytes cleanup _
    writes hBase hLength coherent bounded preimage block]
  exact exec_mapping_scratch spec fields _ _ layout _ baseSlot result
    (.localVar name _ (lookupBinding?_bindValue_same _ _ _) (keccakBytesWord bytes).isLt) hLayout

end Compiler.Proofs.IRGeneration
