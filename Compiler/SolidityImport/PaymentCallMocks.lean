import Verity.Core.Model.Denote
import Lean.Data.Json

/-! Finite bytecode programs for native value and optional-word call tests. -/
namespace Compiler.CompilationModel.SolidityImport.PaymentCallMocks
open Denote ByteExternalCall Verity.Core

private def respond (accounts emptyAccounts : List Nat) (request : Request)
    (world : Verity.ContractState) : Response Verity.ContractState Verity.StorageKey :=
  if request.kind = .staticcall then .exceptional []
  else if emptyAccounts.contains request.target then .success world [] []
  else Id.run do
    let index := accounts.idxOf request.target
    let length := [0, 32, 32, 32, 1, 31, 33, 64, 32].getD index 0
    let value := if index == 1 then 0 else if index == 3 then 2^256-1 else 2
    let data := ((wordBytes value) ++ List.replicate 32 0).take length
    let amount := (request.calldata.drop 36 |>.take 32).foldl
      (fun n b => n * 256 + b.toNat) 0
    let owner := Address.ofNat request.target
    let updated := world.writeAccount owner
      ((world.accountWorld owner).writeStorage 0 (Uint256.ofNat amount))
    let after := updated.writeContractSlot owner.val 0 (Uint256.ofNat amount)
    let touched := [Verity.StorageKey.contractSlot request.target 0]
    if index == 8 then return .revert data touched
    return .success after data touched

/-- Fixed child semantics with ample gas; unknown accounts and low allowances
are instrumentation errors. The source trace independently meters their costs. -/
def environment (accounts emptyAccounts : List Nat) : ByteCallEnvironment :=
  { adversary := some {
      accepts := fun request world =>
        request.kind == .call && request.target != world.thisAddress.val &&
        (accounts.contains request.target || emptyAccounts.contains request.target) &&
        request.gas ≥ 30000
      respond := respond accounts emptyAccounts
      valid := by
        intro request world
        by_cases h : request.kind = .staticcall
        · simp [respond, h, Response.valid]
        · cases respond accounts emptyAccounts request world <;> simp [Response.valid, h] } }

/-- Explicit deployment configuration for the nine fixed response programs. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let accounts ← (← (← input.getObjVal? "paymentChildren").getArr?).toList.mapM Lean.Json.getNat?
  let emptyAccounts ← (← (← input.getObjVal? "emptyChildren").getArr?).toList.mapM Lean.Json.getNat?
  let all := accounts ++ emptyAccounts
  unless accounts.length == 9 && all.eraseDups.length == all.length &&
      all.all (fun n => 256 < n && n < 2^160) do throw "invalid payment child accounts"
  return environment accounts emptyAccounts

end Compiler.CompilationModel.SolidityImport.PaymentCallMocks
