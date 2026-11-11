import Compiler.SolidityImport.RawCallMocks

/-! Independent finite StaticBoolOracle program. Configuration is a CALL;
queries are STATICCALLs with a full calldata-hash check and arbitrary raw output.
Adequate gas and the supplied runtime-code correspondence remain assumptions. -/
namespace Compiler.CompilationModel.SolidityImport.StaticBoolMocks
open Denote ByteExternalCall DenoteByteExternalCalls Verity.Core

/-- Selector of the generic finite program's four-word configuration method. -/
def configurationSelector : Nat := 2344436600

/-- The static branch cannot commit storage effects, including attempted writes. -/
def staticResponse (accounts : List Nat) (request : Request) (world : Verity.ContractState) :
    Bool × Bytes × List Verity.StorageKey := Id.run do
  if !accounts.contains request.target then return (true, [], [])
  let selector := StaticOracleMocks.firstCalldataWord request.calldata / 2^224
  if selector == configurationSelector then return (false, [], [])
  let slot := fun n => (world.storageWords (.contractSlot request.target n)).val
  let touched := (List.range 4).map (Verity.StorageKey.contractSlot request.target)
  let digest := (KeccakEngine.keccak256 (ByteArray.mk request.calldata.toArray)).data.foldl
    (fun n byte => n * 256 + byte.toNat) 0
  if slot 3 != 0 && slot 3 != digest then
    return (false, StaticOracleMocks.calldataMismatchBytes, touched)
  if slot 2 >= 2 then return (false, [], touched)
  return (slot 2 == 0, StaticOracleMocks.responseBytes (slot 0) (slot 1), touched)

/-- Nonstatic configuration writes only the finite program's four slots. -/
def respond (accounts : List Nat) (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if request.kind = .staticcall then (staticAdversary (staticResponse accounts)).respond request world
  else Id.run do
    if !accounts.contains request.target then return .success world [] []
    let word := fun i => StaticOracleMocks.firstCalldataWord (request.calldata.drop (4+i*32))
    let owner := Address.ofNat request.target
    let touched := (List.range 4).map (Verity.StorageKey.contractSlot request.target)
    if word 1 > 128 || word 2 > 3 then return .revert [] touched
    let after := (List.range 4).foldl
      (fun state i => RawCallMocks.writeSlot state owner i (word i)) world
    return .success after [] touched

/-- Reject unknown programs, self calls and requests outside the finite ABI/gas domain. -/
def environment (accounts emptyAccounts : List Nat) : ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some {
      accepts := fun request world =>
        (request.kind == .staticcall || (request.kind == .call &&
          request.calldata.length == 132 &&
          StaticOracleMocks.firstCalldataWord request.calldata / 2^224 == configurationSelector)) &&
        request.value == 0 && request.gas == 1000000 && request.calldata.length ≤ 512 &&
        request.target != world.thisAddress.val &&
        (accounts.contains request.target || emptyAccounts.contains request.target) &&
        (!accounts.contains request.target ||
          (world.storageWords (.contractSlot request.target 1)).val ≤ 128)
      respond := respond accounts
      valid := by
        intro request world
        by_cases h : request.kind = .staticcall
        · simpa only [respond, h, if_pos] using
            (staticAdversary (staticResponse accounts)).valid request world
        · cases respond accounts request world <;> simp [Response.valid, h] } }

/-- Reuse explicit disjoint account validation; program selection never infers code. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  unless (← config.getObjValAs? String "program") == "static-bool-oracle-v1" do
    throw "unsupported static bool oracle program"
  discard (RawCallMocks.configure (input.setObjVal! "byteCallEnvironment"
    (config.setObjVal! "program" (Lean.toJson "raw-context-echo-v1"))))
  let addresses := fun key => do
    (← (← config.getObjVal? key).getArr?).toList.mapM fun value => do
      let text ← value.getStr?
      let some n := text.toNat? | throw "static bool oracle expects decimal addresses"
      pure n
  return environment (← addresses "accounts") (← addresses "emptyAccounts")

end Compiler.CompilationModel.SolidityImport.StaticBoolMocks
