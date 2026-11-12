import Verity.Core.Model.CallGas
import Verity.Core.Model.ByteExternalCall

/-!
Original-bytecode gas evidence for the functional source model. Costs between
observations are measured in the original compiled frame, including dispatcher,
stack operations and memory/storage work. They are never inferred from the
number of source statements. A source-execution adapter must bind this evidence
to the exact runtime bytecode, input, fork and prestate. This executable checker
establishes accounting and ordered boundary agreement, not that provenance.
-/
namespace Compiler.CompilationModel.SourceGas
open ByteExternalCall

/-- A raw call's original-bytecode context and observed child exit. The request
contains the source gas operand; it is replaced with the computed allowance
before invoking the functional callee. Physical memory addresses stay in the
source context because recompilation may allocate a different frame. -/
structure Call where
  context : CallGas.Context
  request : Request
  allowance : Nat
  exceptional : Bool
  gasLeft : Nat
  success : Bool
  returndata : Bytes

/-- A source execution span followed by a boundary. `cost` includes all original
frame instructions since the previous boundary, excluding the next GAS/CALL.
Every supported external call has its own checked boundary; unmetered typed
transports are rejected by the source runner. No cost is silently set to zero. -/
inductive Event where
  | read (site : String) (cost : Nat)
  | call (cost : Nat) (witness : Call)
  | endFrame (cost : Nat)

/-- Remaining source gas and ordered evidence for this one frame. -/
structure State where
  remaining : Nat
  events : List Event

/-- Consume an original-bytecode span, failing rather than saturating on OOG. -/
def consume (state : State) (cost : Nat) : Except String State := do
  let some remaining := CallGas.consume state.remaining cost
    | throw "source gas exhausted before boundary"
  return { state with remaining }

/-- Observe one GAS in its original evaluation position, charging its own cost. -/
def read (state : State) (site : String) : Except String (Nat × State) := do
  let .read expected cost :: rest := state.events
    | throw "missing or reordered source gas observation"
  unless expected == site do throw "source gas observation site differs"
  let state ← consume state cost
  let some remaining := CallGas.observe state.remaining | throw "source GAS out of gas"
  return (remaining, { remaining, events := rest })

/-- Gas operand, target, value and bytes must match the actual original call. -/
def sameRequest (left right : Request) : Bool :=
  left.kind == right.kind && left.caller == right.caller && left.target == right.target &&
    left.value == right.value && left.calldata == right.calldata && left.gas == right.gas

/-- Check the original call operand and derive the actual child allowance. -/
def prepareCall (state : State) (request : Request) :
    Except String (Request × Call × State) := do
  let .call cost witness :: rest := state.events
    | throw "missing or reordered source call gas boundary"
  unless sameRequest request witness.request do throw "source call request differs"
  unless witness.context.transfersValue == (request.kind == .call && request.value != 0) do
    throw "source call value-charge mode differs"
  let state ← consume state cost
  let some charged := CallGas.charge state.remaining request.gas witness.context
    | throw "source call opcode out of gas"
  unless charged.childGas == witness.allowance do
    throw "source child allowance differs from EIP-150 accounting"
  let remaining ← CallGas.finish charged witness.exceptional witness.gasLeft
  unless !witness.exceptional || (!witness.success && witness.returndata.isEmpty) do
    throw "exceptional source child has a success bit or return bytes"
  return ({ request with gas := charged.childGas }, witness, { remaining, events := rest })

/-- Check functional child behavior against the same source call whose gas was
accounted. A response from a different execution cannot be substituted. -/
def checkResponse (witness : Call) (success : Bool) (data : Bytes) : Except String Unit := do
  unless witness.success == success && witness.returndata == data do
    throw "source child outcome differs from functional execution"

/-- A complete frame must consume all gas/call observations, including its tail.
This is a frame budget, not the transaction receipt's refund-adjusted gas usage. -/
def finish (state : State) : Except String Nat := do
  let [.endFrame cost] := state.events | throw "unconsumed source gas evidence"
  return (← consume state cost).remaining

end Compiler.CompilationModel.SourceGas
