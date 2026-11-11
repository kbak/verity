import Compiler.SolidityImport.StaticOracleMocks
import Verity.Core.Model.RawCalls

/-! Independent finite test environment for RawCallOracle's fallback. It models
context-dependent storage and exact calldata echoes. Unknown code, precompiles,
self-reentrant calls and insufficient gas are outside the configured domain. -/
namespace Compiler.CompilationModel.SolidityImport.RawCallMocks
open Denote ByteExternalCall Verity.Core

/-- Persist a child slot in both the flat observation map and account world. -/
def writeSlot (world : Verity.ContractState) (owner : Address) (slot value : Nat) :
    Verity.ContractState :=
  if owner == world.thisAddress then world.writePhysicalSlot slot (Uint256.ofNat value)
  else
    let updated := world.writeAccount owner
      ((world.accountWorld owner).writeStorage slot (Uint256.ofNat value))
    updated.writeContractSlot owner.val slot (Uint256.ofNat value)

/-- Execute the fixed echo program independently of either compiled EVM route. -/
def respond (accounts : List Nat) (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey := Id.run do
  if request.kind = .staticcall then return .exceptional []
  if !accounts.contains request.target then return .success world [] []
  let owner := RawCalls.childAddress request world
  let key := fun slot => if owner == world.thisAddress then Verity.StorageKey.slot slot
    else .contractSlot owner.val slot
  let touched := (List.range 7).map key
  let first := (request.calldata.headD 0).toNat
  if first == 1 then return .revert request.calldata touched
  if first == 2 then return .exceptional touched
  let digest := (KeccakEngine.keccak256 (ByteArray.mk request.calldata.toArray)).data.foldl
    (fun n b => n * 256 + b.toNat) 0
  let values := [digest, (RawCalls.childSender request world).val, owner.val,
    (RawCalls.childValue request world).val, (world.accountWorld owner).balance.val,
    world.txOrigin.val, (world.storageWords (key 6)).val + 1]
  let after := (values.zipIdx).foldl
    (fun state (value, slot) => writeSlot state owner slot value) world
  return .success after request.calldata touched

/-- Reject requests outside the explicit code, gas and input-size domain. -/
def environment (accounts emptyAccounts : List Nat) : ByteCallEnvironment :=
  { adversary := some {
      accepts := fun request world =>
        (request.kind == .call || request.kind == .delegatecall) &&
        request.target != world.thisAddress.val &&
        (accounts.contains request.target || emptyAccounts.contains request.target) &&
        request.gas == 1000000 && request.calldata.length ≤ 1024
      respond := respond accounts
      valid := by
        intro request world
        by_cases h : request.kind = .staticcall
        · simp [respond, h, Response.valid]
        · cases respond accounts request world <;> simp [Response.valid, h] } }

private def address (entry : Lean.Json) : Except String Nat := do
  let text ← entry.getStr?
  let some value := text.toNat? | throw "raw-call mock expects decimal addresses"
  unless value < 2^160 && !StaticOracleMocks.reservedPrecompile value do
    throw "invalid raw-call mock address"
  return value

/-- Configure a disjoint code/empty-account world; never infer missing code. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  unless (← config.getObjValAs? String "program") == "raw-context-echo-v1" do
    throw "unsupported raw-call mock program"
  let caller ← address (← input.getObjVal? "account")
  let accounts ← (← (← config.getObjVal? "accounts").getArr?).toList.mapM address
  let emptyAccounts ← (← (← config.getObjVal? "emptyAccounts").getArr?).toList.mapM address
  let all := caller :: accounts ++ emptyAccounts
  unless all.eraseDups.length == all.length do throw "overlapping raw-call mock accounts"
  return environment accounts emptyAccounts

end Compiler.CompilationModel.SolidityImport.RawCallMocks
