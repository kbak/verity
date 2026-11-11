import Compiler.SolidityImport.Transactions

/-! Explicit zero-fee EOA transaction envelope for named entrypoints. Admission
errors are not EVM reverts. Nonces survive execution failure; incoming value,
callee effects and logs do not. Gas, fees, authorization and EIP-7702 are excluded. -/
namespace Compiler.CompilationModel.SolidityImport.ValueTransactions
open Denote Transactions Verity.Core

/-- Worlds on either side of the reversible value transfer. -/
structure Prepared where
  rollbackWorld : Verity.ContractState
  callWorld : Verity.ContractState

/-- Admit a funded, code-free, distinct sender and advance its nonce before
transferring value. The supplied world already contains the transaction context. -/
def prepare (world : Verity.ContractState) : Except String Prepared := do
  let sender := world.sender
  let target := world.thisAddress
  unless sender != target do throw "value transaction requires a distinct EOA sender"
  let source := world.accountWorld sender
  unless source.code.isEmpty do throw "value transaction requires a code-free sender"
  let some nonce := (if h : source.nonce.val + 1 < 2^64 then
    some (⟨source.nonce.val + 1, h⟩ : Fin (2^64)) else none)
    | throw "transaction nonce exhausted"
  let amount := world.msgValue.val
  unless amount ≤ source.balance.val do throw "insufficient transaction balance"
  let recipient := world.accountWorld target
  unless world.selfBalance == recipient.balance do throw "incoherent recipient balance"
  unless recipient.balance.val + amount < 2^256 do throw "transaction balance overflow"
  let rollbackWorld := world.writeAccount sender { source with nonce }
  let debited := rollbackWorld.writeAccount sender
    { source with nonce, balance := Uint256.ofNat (source.balance.val - amount) }
  let callWorld := debited.writeAccount target
    { recipient with balance := Uint256.ofNat (recipient.balance.val + amount) }
  return { rollbackWorld, callWorld }

/-- Nonpayable checks belong to external entry, not inlined internal helpers. -/
def acceptsValue (fn : FunctionSpec) (value : Nat) : Bool := fn.isPayable || value == 0

/-- Commit successful execution; restore the pre-transfer world on any observed
failure, including ABI rejection, REVERT and INVALID. Sender nonce remains advanced. -/
def settle (prepared : Prepared) (result : FrameResult) : FrameResult :=
  { result with world := if result.success then result.world else prepared.rollbackWorld }

/-- Public Denote entry on an already prepared world. Function denotation itself
remains a body/ABI API; this wrapper adds the external nonpayable guard. -/
def denotePrepared (oracle : DenoteOracle) (model : CompilationModel) (fn : FunctionSpec)
    (tx : DenoteTransaction) (world : Verity.ContractState)
    (byteCalls : ByteCallEnvironment := {}) (calldataSize : Option Nat := none) : DenoteResult :=
  if acceptsValue fn tx.msgValue then
    denoteFunction oracle model fn tx world (byteCalls := byteCalls) (calldataSize := calldataSize)
  else { revertedResult oracle model world with revertData := some [] }

end Compiler.CompilationModel.SolidityImport.ValueTransactions
