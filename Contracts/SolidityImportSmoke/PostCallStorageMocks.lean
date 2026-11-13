import Compiler.SolidityImport.VoidCallMocks
import Mathlib.Tactic.SplitIfs

/-! Independent finite semantics for the ledger and payer test programs.
Only these explicit child addresses and bounded, adequately funded calls are modeled.
The payer reenters the fixture's fixed guarded no-op and neighbor setter. Their
finite semantics are evaluated here from the current world, not recorded EVM rows. -/
namespace Contracts.SolidityImportSmoke.PostCallStorageMocks
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport Denote ByteExternalCall
open Verity.Core

/-- Physical mapping key used by the separately compiled ledger. -/
def balanceSlot (account : Nat) : Nat :=
  (KeccakEngine.keccak256 (ByteArray.mk ((wordBytes account ++ wordBytes 0).toArray))).data.foldl
    (fun n b => n * 256 + b.toNat) 0

/-- Read the current ledger, including short, reverting and exceptional modes. -/
def read (ledger : Nat) (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  let slot := balanceSlot (VoidCallMocks.word request.calldata 4 32)
  let touched := [Verity.StorageKey.contractSlot ledger slot, .contractSlot ledger 1]
  let amount := (world.storageWords (.contractSlot ledger slot)).val
  let mode := (world.storageWords (.contractSlot ledger 1)).val
  if mode == 2 then .revert [0, 65, 0] touched
  else if mode == 3 || mode == 5 then .exceptional touched
  else .success world (if mode == 1 then (wordBytes amount).take 31
    else if mode == 4 then wordBytes amount ++ wordBytes 700
    else if mode == 6 then [] else wordBytes amount) touched

/-- Aggregate the payer's nested credit and exact logs; failed callbacks commit nothing. -/
def pay (ledger payer : Nat) (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey := Id.run do
  let paid := VoidCallMocks.word request.calldata 36 32
  let mode := VoidCallMocks.word request.calldata 68 32
  let size := VoidCallMocks.word request.calldata 132 32
  let slot := balanceSlot world.thisAddress.val
  let touched := [Verity.StorageKey.contractSlot ledger slot, .contractSlot ledger 1,
    .contractSlot payer 0, .slot 1]
  if mode == 7 then return .revert [0, 82, 0] touched
  if mode == 8 then return .exceptional touched
  let flags := (world.storage 1).val
  -- The view must report locked; guardedPing then reverts with Error("locked").
  -- Neither nested call changes state. The following unguarded setter does.
  if (flags / 2^128) % 256 != 0 then return .revert (errorStringBytes "unlocked") touched
  let balance := (world.storageWords (.contractSlot ledger slot)).val
  let count := (world.storageWords (.contractSlot payer 0)).val
  let world := RawCallMocks.writeSlot world (Address.ofNat ledger) slot (balance + paid)
  let world := RawCallMocks.writeSlot world (Address.ofNat ledger) 1 mode
  let world := EventLogs.append world
    { emitter := Address.ofNat ledger, topics := [], data := wordBytes paid }
  let neighbor : Nat := paid % 2^128
  let world := world.modifyPhysicalSlots [1]
    (fun current => Uint256.ofNat ((current.val / 2^128) * 2^128 + neighbor))
  let topic := (KeccakEngine.keccak256 "Changed(uint256)".toUTF8).data.foldl
    (fun n b => n * 256 + b.toNat) 0
  let world := EventLogs.append world
    { emitter := world.thisAddress, topics := [Uint256.ofNat topic], data := wordBytes neighbor }
  let world := RawCallMocks.writeSlot world (Address.ofNat payer) 0 (count + 1)
  let world := EventLogs.append world
    { emitter := Address.ofNat payer, topics := [], data := wordBytes mode }
  return .success world ((request.calldata.drop 164).take size) touched

/-- The two child entrypoints have a closed request domain; other requests are errors. -/
def environment (ledger payer readSelector paySelector : Nat) : ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some {
      accepts := fun request _ =>
        request.value == 0 &&
        (if request.kind == .staticcall then
          request.target == ledger && request.gas ≥ 10000 &&
          request.calldata.length == 36 &&
          VoidCallMocks.word request.calldata 0 4 == readSelector
        else request.kind == .call && request.target == payer && request.gas ≥ 100000 &&
          VoidCallMocks.word request.calldata 0 4 == paySelector &&
          VoidCallMocks.word request.calldata 4 32 == ledger &&
          VoidCallMocks.word request.calldata 100 32 == 128 &&
          VoidCallMocks.word request.calldata 132 32 ≤ 128 &&
          request.calldata.length == 164 +
            ((VoidCallMocks.word request.calldata 132 32 + 31) / 32) * 32)
      respond := fun request world =>
        if request.kind = .staticcall then read ledger request world
        else pay ledger payer request world
      valid := by
        intro request world
        split
        · dsimp only [read]
          split_ifs <;> simp only [Response.valid, implies_true]
        · rename_i nonstatic
          cases pay ledger payer request world <;> simp only [Response.valid, nonstatic,
            false_implies] } }

/-- Validate explicit disjoint account identities before configuring the finite program. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  unless (← config.getObjValAs? String "program") == "post-call-storage-v1" do
    throw "unsupported post-call balance program"
  let legacy := input.setObjVal! "byteCallEnvironment"
    (config.setObjVal! "program" (Lean.toJson "raw-context-echo-v1"))
  discard (RawCallMocks.configure legacy)
  let accounts ← (← (← config.getObjVal? "accounts").getArr?).toList.mapM fun value => do
    let some n := (← value.getStr?).toNat? | throw "invalid balance child address"
    pure n
  let [ledger, payer] := accounts | throw "expected ledger and payer addresses"
  let readSelector ← config.getObjValAs? Nat "readSelector"
  let paySelector ← config.getObjValAs? Nat "paySelector"
  unless readSelector < 2^32 && paySelector < 2^32 do throw "invalid child selector"
  return environment ledger payer readSelector paySelector
end Contracts.SolidityImportSmoke.PostCallStorageMocks
