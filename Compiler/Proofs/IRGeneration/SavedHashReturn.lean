import Compiler.Proofs.IRGeneration.BindingMstoreExecution
import Compiler.Proofs.IRGeneration.MemorySliceBridge

namespace Compiler.Proofs.IRGeneration

open Compiler Compiler.Yul Compiler.CompilationModel SourceSemantics
open Compiler.CompilationModel.DenoteMemory Compiler.CompilationModel.PhysicalMemory

/-- The EVM word obtained by hashing the exact byte string, including a partial final word. -/
def keccakBytesWord (bytes : ByteArray) : Verity.Core.Uint256 :=
  Verity.Core.Uint256.ofNat (KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 bytes))

/-- A canonical hash reads the physical preimage at the evaluated offset and length. -/
theorem eval_canonical_keccak_of_physical_slice (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (base length : Expr) (offset size : Nat) (bytes : ByteArray)
    (hBase : evalExprCanonical spec fields state base = some offset)
    (hLength : evalExprCanonical spec fields state length = some size)
    (coherent : Coherent state.world)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (preimage : state.world.byteMemory.sliceBytes offset size = bytes) :
    evalExprCanonical spec fields state (.keccak256 base length) =
      some (keccakBytesWord bytes).val := by
  unfold evalExprCanonical at hBase hLength ⊢
  rw [evalExprWithHelpers.eq_def]
  simp only [hBase, hLength, keccakMemorySlice]
  subst bytes
  exact congrArg some (abstract_keccak_memory_slice_eq_physical state.world coherent
    offset size bounded)

/-- A continuing statement prefix passes its entire poststate to the suffix. -/
theorem exec_canonical_append_of_continue (spec : CompilationModel) (fields : List Field)
    (state next : RuntimeState) (prefixStmts suffix : List Stmt)
    (run : execStmtsCanonical spec fields state prefixStmts = .continue next) :
    execStmtsCanonical spec fields state (prefixStmts ++ suffix) =
      execStmtsCanonical spec fields next suffix := by
  induction prefixStmts generalizing state with
  | nil =>
      rw [execStmtsCanonical_nil] at run
      cases run
      rfl
  | cons stmt rest ih =>
      rw [List.cons_append]
      unfold execStmtsCanonical at run ⊢
      rw [execStmtListWithHelpers.eq_def] at run ⊢
      cases step : execStmtWithHelpers spec fields 0 state stmt <;> simp only [step] at run ⊢
      · exact ih _ run
      all_goals cases run

private theorem exec_return_bound_word (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (name : String) (word : Verity.Core.Uint256)
    (found : lookupValue state.bindings name = word.val) :
    execStmtsCanonical spec fields state [.returnValues [.localVar name]] =
      .stop { state with observedReturnWords := some [word.val] } := by
  unfold execStmtsCanonical
  rw [execStmtListWithHelpers.eq_def]
  simp only
  rw [execStmtWithHelpers.eq_def]
  simp only
  have localEval : evalExpr fields state (.localVar name) = some word.val := by
    rw [evalExpr.eq_def]
    exact congrArg some found
  simp [evalExprList, localEval, wordNormalize_eq_mod]
  exact word.isLt

/-- Capture the digest before a witnessed cleanup and pass the exact poststate to the caller. -/
theorem exec_saved_hash_cleanup_then (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (name : String) (base length : Expr) (offset size : Nat)
    (bytes : ByteArray) (cleanup suffix : List Stmt) (writes : List (Nat × Verity.Core.Uint256))
    (hBase : evalExprCanonical spec fields state base = some offset)
    (hLength : evalExprCanonical spec fields state length = some size)
    (coherent : Coherent state.world)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (preimage : state.world.byteMemory.sliceBytes offset size = bytes)
    (block : BindingMstoreBlock (bindValue state.bindings name (keccakBytesWord bytes).val)
      cleanup writes) :
    let saved := { state with
      bindings := bindValue state.bindings name (keccakBytesWord bytes).val }
    execStmtsCanonical spec fields state (.assignVar name (.keccak256 base length) ::
      (cleanup ++ suffix)) =
        execStmtsCanonical spec fields (mstoreBlockState saved writes) suffix := by
  dsimp only
  let saved := { state with bindings := bindValue state.bindings name (keccakBytesWord bytes).val }
  have digest := eval_canonical_keccak_of_physical_slice spec fields state base length offset
    size bytes hBase hLength coherent bounded preimage
  have capture : execStmtCanonical spec fields state (.assignVar name (.keccak256 base length)) =
      .continue saved := by
    unfold evalExprCanonical at digest
    simp only [execStmtCanonical, execStmtWithHelpers.eq_def, digest, saved]
  rw [exec_canonical_cons_of_continue spec fields state saved _ _ capture,
    exec_canonical_append_of_continue spec fields saved _ cleanup _
      (exec_binding_mstore_block spec fields saved cleanup writes block)]

/-- Capture the original hash, run the witnessed stores, and return the saved binding.
Stores may overwrite the preimage. The result specifies both the returned word and the poststate. -/
theorem exec_saved_hash_return (spec : CompilationModel) (fields : List Field)
    (state : RuntimeState) (name : String) (base length : Expr) (offset size : Nat)
    (bytes : ByteArray) (cleanup : List Stmt) (writes : List (Nat × Verity.Core.Uint256))
    (hBase : evalExprCanonical spec fields state base = some offset)
    (hLength : evalExprCanonical spec fields state length = some size)
    (coherent : Coherent state.world)
    (bounded : offset + byteWordCount size * 32 ≤ Compiler.Constants.evmModulus)
    (preimage : state.world.byteMemory.sliceBytes offset size = bytes)
    (block : BindingMstoreBlock (bindValue state.bindings name (keccakBytesWord bytes).val)
      cleanup writes) :
    let saved := { state with
      bindings := bindValue state.bindings name (keccakBytesWord bytes).val }
    execStmtsCanonical spec fields state
        (.assignVar name (.keccak256 base length) ::
          (cleanup ++ [.returnValues [.localVar name]])) =
      .stop { mstoreBlockState saved writes with
        observedReturnWords := some [(keccakBytesWord bytes).val] } := by
  dsimp only
  rw [exec_saved_hash_cleanup_then spec fields state name base length offset size bytes cleanup _
    writes hBase hLength coherent bounded preimage block]
  apply exec_return_bound_word
  exact lookupValue_bindValue_same _ _ _

/-- The external singleton return stores the local at zero and returns 32 bytes. -/
theorem compile_return_local_word (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (source : DynamicDataSource) (scope : List String)
    (adts : List AdtTypeDef) (functions : List FunctionSpec) (name : String) :
    compileStmt fields events errors source [] false scope adts (.returnValues [.localVar name])
        functions =
      .ok [.exprStmt (.call "mstore" [.lit 0, .ident name]),
        .exprStmt (.call "return" [.lit 0, .lit 32])] := by
  unfold compileStmt
  rw [compileStmtWithFork.eq_def]
  simp only [Bool.false_eq_true, ↓reduceIte, List.isEmpty_cons]
  rw [compileExprListWithInternals.eq_def]
  simp only
  rw [compileExprWithInternals.eq_def, compileExprListWithInternals.eq_def]
  rfl

/-- The actual IR return sequence reads the saved local and returns its normalized word. -/
theorem exec_ir_return_local_word (state : IRState) (name : String) (word : Verity.Core.Uint256)
    (fuel : Nat) (found : state.getVar name = some word.val) :
    execIRStmts (fuel + 3) state
        [.exprStmt (.call "mstore" [.lit 0, .ident name]),
         .exprStmt (.call "return" [.lit 0, .lit 32])] =
      .return word.val (state.writePhysicalMemoryValue 0 word.val) := by
  have bounded : word.val < Verity.Core.Uint256.modulus := word.isLt
  simp only [execIRStmts, execIRStmt, evalIRExpr, found, ↓reduceIte,
    Verity.Core.Uint256.val_ofNat, Nat.zero_mod, IRState.writePhysicalMemoryValue_at,
    Nat.mod_eq_of_lt bounded]

/-- Each byte of the ABI return window is the corresponding big-endian byte of the saved word. -/
theorem ir_return_local_word_byte (state : IRState) (word : Verity.Core.Uint256) (index : Fin 32) :
    (state.writePhysicalMemoryValue 0 word.val).byteMemory.readByte index.val =
      valueWord word index := by
  have normalized : Verity.Core.Uint256.ofNat word.val = word := by
    apply Verity.Core.Uint256.ext
    exact Nat.mod_eq_of_lt word.isLt
  simpa only [IRState.writePhysicalMemoryValue, IRState.installPhysicalMemory, normalized,
    Nat.zero_add] using
    (Memory.readByte_writeWord_at state.byteMemory 0 (valueWord word) index)

/-- The compiled external return produces the saved word and its exact ABI bytes. -/
theorem exec_compiled_return_local_word (fields : List Field) (events : List EventDef)
    (errors : List ErrorDef) (source : DynamicDataSource) (scope : List String)
    (adts : List AdtTypeDef) (functions : List FunctionSpec) (name : String)
    (code : List YulStmt) (state : IRState) (word : Verity.Core.Uint256) (fuel : Nat)
    (compiled : compileStmt fields events errors source [] false scope adts
      (.returnValues [.localVar name]) functions = .ok code)
    (found : state.getVar name = some word.val) :
    ∃ final, execIRStmts (fuel + 3) state code = .return word.val final ∧
      ∀ index : Fin 32, final.byteMemory.readByte index.val = valueWord word index := by
  rw [compile_return_local_word] at compiled
  cases compiled
  exact ⟨_, exec_ir_return_local_word state name word fuel found,
    ir_return_local_word_byte state word⟩

end Compiler.Proofs.IRGeneration
