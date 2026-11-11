import Compiler.SolidityImport.ValueTransactions

/-! Transaction-envelope properties; these do not prove Solidity correspondence. -/
namespace Compiler.CompilationModel.SolidityImport.ValueTransactions
open Transactions Verity.Core

/-- Failure restores the world reserved before the value transfer. -/
theorem settle_failure_world (prepared : Prepared) (result : FrameResult)
    (failed : result.success = false) :
    (settle prepared result).world = prepared.rollbackWorld := by
  simp only [settle, failed, Bool.false_eq_true, ↓reduceIte]

/-- Success preserves every observed callee effect. -/
theorem settle_success_world (prepared : Prepared) (result : FrameResult)
    (succeeded : result.success = true) :
    (settle prepared result).world = result.world := by
  simp only [settle, succeeded, ↓reduceIte]

/-- Every rejected nonpayable entry has nonzero incoming value. -/
theorem acceptsValue_nonpayable (fn : FunctionSpec) (value : Nat)
    (nonpayable : fn.isPayable = false) : acceptsValue fn value = true ↔ value = 0 := by
  simp only [acceptsValue, nonpayable, Bool.false_or, beq_iff_eq]

/-- Preparation conserves the combined sender/recipient balance, before any body runs. -/
theorem prepare_conserves_balances (world : Verity.ContractState) (prepared : Prepared)
    (executed : prepare world = .ok prepared) :
    (prepared.callWorld.accountWorld world.sender).balance.val +
      (prepared.callWorld.accountWorld world.thisAddress).balance.val =
    (world.accountWorld world.sender).balance.val +
      (world.accountWorld world.thisAddress).balance.val := by
  simp only [prepare, bind, Except.bind, pure, Except.pure, throw, throwThe] at executed
  repeat' split at executed
  all_goals cases executed
  all_goals try contradiction
  all_goals simp_all only [bne_iff_ne, ne_eq, beq_iff_eq]
  all_goals
    rw [Verity.ContractState.writeAccount_other _ _ _ _ (by assumption)]
    simp only [Verity.ContractState.writeAccount_at, Uint256.val_ofNat]
    have bounded := (world.accountWorld world.sender).balance.isLt
    simp only [Uint256.modulus, UINT256_MODULUS] at *
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The rollback world reserves exactly the sender's next nonce. -/
theorem prepare_reserves_nonce (world : Verity.ContractState) (prepared : Prepared)
    (executed : prepare world = .ok prepared) :
    (prepared.rollbackWorld.accountWorld world.sender).nonce.val =
      (world.accountWorld world.sender).nonce.val + 1 := by
  simp only [prepare, bind, Except.bind, pure, Except.pure, throw, throwThe] at executed
  repeat' split at executed
  all_goals cases executed
  all_goals try contradiction
  all_goals split at *
  all_goals simp_all only [Option.some.injEq, reduceCtorEq,
    Verity.ContractState.writeAccount_at]
  all_goals
    rename_i same
    exact congrArg Fin.val same.symm

end Compiler.CompilationModel.SolidityImport.ValueTransactions
