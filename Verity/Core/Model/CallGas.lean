import Verity.Core.Model.Create2ParentGas

/-!
CALL/DELEGATECALL gas at an actual bytecode boundary, for Cancun through Osaka.
Account warmth, death and optional EIP-7702 delegation are execution-context
inputs. They must come from the source EVM, not from the functional world model.
The memory ranges and pre-opcode gas are likewise source-bytecode quantities.
This module does not assign opcode costs to high-level Solidity statements.
-/
namespace Compiler.CompilationModel.CallGas

/-- Source CALL context. For DELEGATECALL, `transfersValue` must be false even
when the inherited msg.value is nonzero. `delegationWarm` is absent for ordinary
code; when present it records the warmth of the resolved EIP-7702 code address. -/
structure Context where
  memoryWords : Nat
  inputOffset : Nat
  inputSize : Nat
  outputOffset : Nat := 0
  outputSize : Nat := 0
  targetWarm : Bool
  targetDead : Bool
  transfersValue : Bool
  delegationWarm : Option Bool := none
  deriving DecidableEq, Repr

/-- Post-expansion active memory size; zero-length regions ignore their offset. -/
def memoryWords (ctx : Context) : Nat :=
  Create2ParentGas.resultingWords
    (Create2ParentGas.resultingWords ctx.memoryWords ctx.inputOffset ctx.inputSize)
    ctx.outputOffset ctx.outputSize

/-- EIP-2929 account-access charge. -/
def accessCost (warm : Bool) : Nat := if warm then 100 else 2600

/-- Opcode overhead before applying the EIP-150 cap. Value transfer and account
creation costs apply only to CALL with nonzero value. Delegation access is the
additional EIP-7702 code lookup, not a second charge for an ordinary target. -/
def overhead (ctx : Context) : Nat :=
  accessCost ctx.targetWarm +
    (ctx.delegationWarm.map accessCost).getD 0

/-- Complete pre-forwarding cost, including expansion of both memory regions. -/
def opcodeCost (ctx : Context) : Nat :=
  overhead ctx + (if ctx.transfersValue then 9000 + (if ctx.targetDead then 25000 else 0)
    else 0) +
  (Create2ParentGas.memoryCost (memoryWords ctx) -
    Create2ParentGas.memoryCost ctx.memoryWords)

/-- A call retains its parent reserve and lends the capped allowance to the
child. The value stipend is part of child gas, but not of the capped operand. -/
structure Charged where
  opcodeGas : Nat
  memoryWords : Nat
  forwardedGas : Nat
  stipend : Nat
  reservedGas : Nat
  deriving DecidableEq, Repr

/-- Actual initial gas in the child frame, including the value stipend. -/
def Charged.childGas (state : Charged) : Nat := state.forwardedGas + state.stipend

/-- An unaffordable opcode fails in the parent. An oversized gas operand is
capped after overhead, rather than causing an out-of-gas error. -/
def charge (available requested : Nat) (ctx : Context) : Option Charged :=
  let cost := opcodeCost ctx
  if cost ≤ available then
    let remaining := available - cost
    let forwarded := min requested (remaining - remaining / 64)
    some {
      opcodeGas := cost
      memoryWords := memoryWords ctx
      forwardedGas := forwarded
      stipend := if ctx.transfersValue then 2300 else 0
      reservedGas := remaining - forwarded }
  else none

/-- Child exceptional halts return no gas. Success and REVERT return only
unspent allowance. A depth/balance failure returns the unused entire allowance.
The latter is represented by `exceptional = false` and `left = childGas`. -/
def finish (state : Charged) (exceptional : Bool) (left : Nat) : Except String Nat :=
  if left > state.childGas then .error "child returned gas above its allowance"
  else if exceptional && left != 0 then .error "exceptional child returned gas"
  else .ok (state.reservedGas + left)

/-- GAS charges its own two gas before exposing the remaining balance. -/
def observe (available : Nat) : Option Nat :=
  if 2 ≤ available then some (available - 2) else none

/-- Generic cost charging for source bytecode spans between observed boundaries.
A span's cost is supplied by the original-bytecode executor, not estimated from
Solidity or generated Yul. Correspondence to that bytecode is a separate duty. -/
def consume (available cost : Nat) : Option Nat :=
  if cost ≤ available then some (available - cost) else none

end Compiler.CompilationModel.CallGas
