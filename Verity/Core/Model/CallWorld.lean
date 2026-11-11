import Verity.Core

/-! Persistent call effects and caller execution-context restoration. -/
namespace Compiler.CompilationModel.CallWorld

/-- Commit a callee's persistent world into the caller: storage, account,
balance, code, log and call-journal channels come from `callee`, while the
caller's execution context, calldata, memories and legacy returndata stay. -/
def commitCalleeWorld (caller callee : Verity.ContractState) : Verity.ContractState :=
  { callee with
    sender := caller.sender
    thisAddress := caller.thisAddress
    txOrigin := caller.txOrigin
    msgValue := caller.msgValue
    blockTimestamp := caller.blockTimestamp
    blockNumber := caller.blockNumber
    chainId := caller.chainId
    blobBaseFee := caller.blobBaseFee
    baseFee := caller.baseFee
    gasPrice := caller.gasPrice
    calldataSize := caller.calldataSize
    calldata := caller.calldata
    selector := caller.selector
    memory := caller.memory
    byteMemory := caller.byteMemory
    returndata := caller.returndata }


end Compiler.CompilationModel.CallWorld
