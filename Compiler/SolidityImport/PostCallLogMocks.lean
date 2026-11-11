import Compiler.SolidityImport.RawCallMocks

/-! Finite independent program for PostCallLogOracle: exact LOG0..LOG4 payloads,
bounded nested CALL/DELEGATECALL, and storage/log rollback. This is test evidence,
not a general external-bytecode evaluator. Gas/resource adequacy is assumed. -/
namespace Compiler.CompilationModel.SolidityImport.PostCallLogMocks
open Denote ByteExternalCall Verity.Core

/-- All opcode records include the execution account, even for a delegated child. -/
def record (world : Verity.ContractState) (owner : Address) (data : Bytes)
    (topics : List Nat) : Verity.ContractState :=
  EventLogs.append world { emitter := owner, topics := topics.map Uint256.ofNat, data }

/-- Execute the finite program. Fuel bounds the configured domain; exhaustion is
an instrumentation error. The full caller world is retained as the rollback point. -/
def evaluate (accounts emptyAccounts : List Nat) : Nat → Address → Address → Uint256 →
    Nat → Bytes → Verity.ContractState →
    Except String (Response Verity.ContractState Verity.StorageKey)
  | 0, _, _, _, _, _, _ => .error "log mock nesting outside configured domain"
  | fuel + 1, owner, sender, value, target, data, before => do
      if emptyAccounts.contains target then return .success before [] []
      unless accounts.contains target do throw "unknown log mock code"
      let key := if owner == before.thisAddress then Verity.StorageKey.slot 7
        else .contractSlot owner.val 7
      let world := RawCallMocks.writeSlot before owner 7 ((before.storageWords key).val + 1)
      let world := [[], [owner.val], [sender.val, value.val], [0x33, owner.val, sender.val],
        [0x44, owner.val, sender.val, value.val]].foldl
          (fun state topics => record state owner data topics) world
      let mode := (data.headD 0).toNat
      if mode == 1 then return .revert data [key]
      if mode == 2 then return .exceptional [key]
      if 2 < mode && mode < 6 then
        unless 21 ≤ data.length do throw "nested log mock header is truncated"
        let target := ((data.drop 1).take 20).foldl (fun n b => n * 256 + b.toNat) 0
        let delegated := mode == 4
        let childOwner := if delegated then owner else Address.ofNat target
        let childSender := if delegated then sender else owner
        let childValue := if delegated then value else 0
        let child ← evaluate accounts emptyAccounts fuel childOwner childSender childValue
          target (data.drop 21) world
        let world := record (child.commit world) owner data [0x55, if child.succeeded then 1 else 0]
        if mode == 5 then return .revert data (key :: child.accesses)
        return .success world data (key :: child.accesses)
      return .success world data [key]

/-- Static requests always fail; valid nonstatic responses come from the checked program. -/
def respond (accounts emptyAccounts : List Nat) (request : Request)
    (world : Verity.ContractState) : Response Verity.ContractState Verity.StorageKey :=
  if request.kind = .staticcall then .exceptional [] else
    match evaluate accounts emptyAccounts 3 (RawCalls.childAddress request world)
        (RawCalls.childSender request world) (RawCalls.childValue request world)
        request.target request.calldata world with
    | .ok response => response
    | .error _ => .exceptional []

/-- Unknown programs, gas bounds and malformed nesting fail admission, never fabricate reverts. -/
def environment (accounts emptyAccounts : List Nat) : ByteCallEnvironment :=
  { adversary := some {
      accepts := fun request world =>
        (request.kind == .call || request.kind == .delegatecall) &&
        request.target != world.thisAddress.val && request.gas == 1000000 &&
        request.calldata.length ≤ 512 &&
        (evaluate accounts emptyAccounts 3 (RawCalls.childAddress request world)
          (RawCalls.childSender request world) (RawCalls.childValue request world)
          request.target request.calldata world).isOk
      respond := respond accounts emptyAccounts
      valid := by
        intro request world
        by_cases h : request.kind = .staticcall
        · simp [respond, h, Response.valid]
        · cases respond accounts emptyAccounts request world <;> simp [Response.valid, h] } }

/-- Reuse the explicit disjoint-address admission of the raw-call fixture. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  unless (← config.getObjValAs? String "program") == "post-call-logs-v1" do
    throw "unsupported post-call log mock program"
  let legacy := input.setObjVal! "byteCallEnvironment"
    (config.setObjVal! "program" (Lean.toJson "raw-context-echo-v1"))
  discard (RawCallMocks.configure legacy)
  let addresses := fun key => do
    (← (← config.getObjVal? key).getArr?).toList.mapM fun value => do
      let text ← value.getStr?
      let some n := text.toNat? | throw "log mock expects decimal addresses"
      pure n
  return environment (← addresses "accounts") (← addresses "emptyAccounts")

end Compiler.CompilationModel.SolidityImport.PostCallLogMocks
