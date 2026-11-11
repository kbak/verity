import Verity.Core.Model.CallWorld
import Verity.Core.Model.ByteExternalCall
import Verity.Core.Model.EventLogs

/-! Functional CALL/DELEGATECALL boundary. Gas and call-depth behavior are
obligations of the explicit external environment, not computed by this model.
The request's caller is the executing account; delegate frames inherit sender
and value from the supplied parent world. -/
namespace Compiler.CompilationModel.RawCalls
open ByteExternalCall Verity.Core

/-- Address whose storage and balance the child executes against. -/
def childAddress (request : Request) (world : Verity.ContractState) : Address :=
  if request.kind == .delegatecall then world.thisAddress else Address.ofNat request.target

/-- DELEGATECALL preserves the parent sender; CALL uses the executing account. -/
def childSender (request : Request) (world : Verity.ContractState) : Address :=
  if request.kind == .delegatecall then world.sender else world.thisAddress

/-- DELEGATECALL inherits msg.value without making another value transfer. -/
def childValue (request : Request) (world : Verity.ContractState) : Uint256 :=
  if request.kind == .delegatecall then world.msgValue else Uint256.ofNat request.value

/-- Debit and credit before child execution. Insufficient funds fail the call;
self-calls still check funds but leave balances unchanged. An impossible balance
overflow is an instrumentation error, not wrapped ether. -/
def transferValue (world : Verity.ContractState) (target : Address) (amount : Nat) :
    Except String (Option Verity.ContractState) := do
  let source := world.thisAddress
  let account := world.accountWorld source
  unless world.selfBalance == account.balance do throw "incoherent caller balance"
  if amount > account.balance.val then return none
  if source == target then return some world
  let recipient := world.accountWorld target
  unless recipient.balance.val + amount < 2^256 do throw "recipient balance overflow"
  let paid := world.writeAccount source
    { account with balance := Uint256.ofNat (account.balance.val - amount) }
  return some (paid.writeAccount target
    { recipient with balance := Uint256.ofNat (recipient.balance.val + amount) })

/-- Execute the explicit child against its prepared world. Failed children roll
back the transfer and all persistent effects while retaining their exact bytes
and accesses. Success commits persistent effects and restores parent context. -/
def execute (adversary : Adversary Verity.ContractState Verity.StorageKey)
    (request : Request) (before : Verity.ContractState) :
    Except String (Observation Verity.ContractState Verity.StorageKey) := do
  unless request.kind == .call || request.kind == .delegatecall do
    throw "raw call requires CALL or DELEGATECALL"
  unless request.caller == before.thisAddress.val && request.target < 2^160 &&
      request.value < 2^256 do throw "invalid raw call request"
  if request.kind == .delegatecall && request.value != before.msgValue.val then
    throw "delegatecall value differs from parent frame"
  let prepared ← if request.kind == .call then
    transferValue before (Address.ofNat request.target) request.value
    else pure (some before)
  let some prepared := prepared
    | return { success := false, world := before, returndata := [], touched := [] }
  let observed ← executeChecked adversary request prepared
  unless !observed.success || EventLogs.validExtension before.events observed.world.events do
    throw "raw-call success must preserve prior logs and append complete EVM logs"
  return { observed with world := if observed.success then
    CallWorld.commitCalleeWorld before observed.world else before }

end Compiler.CompilationModel.RawCalls
