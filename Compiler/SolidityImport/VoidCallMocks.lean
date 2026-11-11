import Compiler.SolidityImport.RawCallMocks

/-! Independent finite child program for VoidCallOracle. It records exact call
input/context, rejects selected phases and returns untyped bytes. Unknown code,
self reentrancy and resource exhaustion remain outside the test environment. -/
namespace Compiler.CompilationModel.SolidityImport.VoidCallMocks
open Denote ByteExternalCall Verity.Core

/-- Big-endian input word; missing bytes are zero, as in CALLDATALOAD. -/
def word (data : Bytes) (offset size : Nat) : Nat :=
  (List.range size).foldl (fun n i => n * 256 + (data.getD (offset+i) 0).toNat) 0

/-- Execute the finite fixture independently of both compiled EVM routes. -/
def respond (accounts : List Nat) (beforeSelector afterSelector modeOffset : Nat)
    (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey := Id.run do
  if request.kind = .staticcall then return .exceptional []
  if !accounts.contains request.target then return .success world [] []
  let owner := RawCalls.childAddress request world
  let key := fun slot => if owner == world.thisAddress then Verity.StorageKey.slot slot
    else .contractSlot owner.val slot
  let data := request.calldata
  let selector := word data 0 4
  let before := selector == beforeSelector
  let after := selector == afterSelector
  let mode := if before then word data modeOffset 32
    else if after then (world.storageWords (key 20)).val
    else (data.headD 0).toNat
  let touched := (List.range 6).map (fun i => key (20+i))
  if (before && mode == 200) || (after && mode == 202) ||
      (!before && !after && mode == 1) then return .revert data touched
  if (before && mode == 201) || (after && mode == 203) ||
      (!before && !after && mode == 2) then return .exceptional touched
  let world := if before then RawCallMocks.writeSlot world owner 20 mode else world
  let digest := (KeccakEngine.keccak256 (ByteArray.mk data.toArray)).data.foldl
    (fun n b => n * 256 + b.toNat) 0
  let values := [(world.storageWords (key 21)).val + 1, digest,
    (RawCalls.childSender request world).val, owner.val, (RawCalls.childValue request world).val]
  let world := values.zipIdx.foldl
    (fun state (value, i) => RawCallMocks.writeSlot state owner (21+i) value) world
  let world := EventLogs.append world { emitter := owner, topics := [], data }
  let returned := if before || after then (List.range (mode % 128)).map (data.getD · 0) else data
  return .success world returned touched

/-- The scalar CALL gas setting represents an independently adequate budget;
this bounded program does not assert gas equivalence. -/
def environment (accounts emptyAccounts : List Nat)
    (beforeSelector afterSelector modeOffset : Nat) :
    ByteCallEnvironment :=
  { gas := some 1000000
    adversary := some {
      accepts := fun request world =>
        (request.kind == .call || request.kind == .delegatecall) &&
        request.target != world.thisAddress.val &&
        (accounts.contains request.target || emptyAccounts.contains request.target) &&
        request.gas == 1000000 && request.calldata.length ≤ 4096
      respond := respond accounts beforeSelector afterSelector modeOffset
      valid := by
        intro request world
        by_cases h : request.kind = .staticcall
        · simp [respond, h, Response.valid]
        · cases respond accounts beforeSelector afterSelector modeOffset request world <;>
            simp [Response.valid, h] } }

/-- Require explicit, disjoint addresses with checked code membership. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  unless (← config.getObjValAs? String "program") == "void-callbacks-v1" do
    throw "unsupported void callback mock program"
  let legacy := input.setObjVal! "byteCallEnvironment"
    (config.setObjVal! "program" (Lean.toJson "raw-context-echo-v1"))
  discard (RawCallMocks.configure legacy)
  let addresses := fun key => do
    (← (← config.getObjVal? key).getArr?).toList.mapM fun value => do
      let text ← value.getStr?
      let some n := text.toNat? | throw "callback mock expects decimal addresses"
      pure n
  let setting := fun key fallback => do
    match config.getObjVal? key with
    | .error _ => pure fallback
    | .ok value => value.getNat?
  let before ← setting "beforeSelector" 2894857179
  let after ← setting "afterSelector" 1528555473
  let offset ← setting "modeOffset" 132
  unless before < 2^32 && after < 2^32 && before != after && offset < 4096 do
    throw "invalid callback mock ABI layout"
  return environment (← addresses "accounts") (← addresses "emptyAccounts") before after offset

end Compiler.CompilationModel.SolidityImport.VoidCallMocks
