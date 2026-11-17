import Compiler.SolidityImport.ObservedImport
import Compiler.SolidityImport.ControlDenote
import Compiler.SolidityImport.Transactions
import Compiler.SolidityImport.EventObservation

/-! Downstream frame execution for explicitly imported observed programs.
No dispatch, arbitrary calldata decoding, gas bound or refinement is asserted. -/

namespace Compiler.CompilationModel.SolidityImport.ObservedExecution
open Denote

/-- Find exactly one selected root. Hand-constructed slices must not hide duplicate names. -/
def findRoot (slice : ObservedImport.Slice) (name : String) : Except String ObservedImport.Root :=
  match slice.functions.filter (·.name == name) with
  | [fn] => .ok fn.root
  | [] => .error s!"unknown observed root: {name}"
  | _ => .error s!"ambiguous observed root: {name}"

/-- Require exactly one canonical ABI word per scalar parameter. Noncanonical inputs
are outside this adapter's scope, not simulated Solidity reverts. -/
def bindCanonical (params : List Param) (args : List Nat) : Except String Denote.Env := do
  unless params.length == args.length do throw "observed argument count mismatch"
  unless (params.zip args).all (fun (p, word) =>
      decodeSupportedParamWord p.ty word == some word) do
    throw "observed arguments must be canonical scalar ABI words"
  let some bindings := bindSupportedParams params args
    | throw "unsupported observed parameter type"
  return bindings

/-- Observe one nonpayable frame using an explicit budget. `none` publishes no
outcome or partial state; errors remain adapter failures. Only completed source
outcomes pass through the ordinary commit/rollback boundary. The caller supplies
the transaction environment and canonical scalar words, not arbitrary calldata. -/
def executeRoot (root : ObservedImport.Root) (oracle : DenoteOracle) (fuel : Nat)
    (world : Verity.ContractState) (args : List Nat) :
    Except String (Option Transactions.FrameResult) := do
  let bindings ← bindCanonical root.control.params args
  unless world.msgValue == 0 do throw "observed frames require zero call value"
  let initial := Transactions.beginTransaction world
  match ControlDenote.observe oracle root.fields fuel root.control.body
      { world := initial, bindings } with
  | none => return none
  | some (.error message) => throw message
  | some (.ok (.normal _)) => throw "observed frame fell through without a source outcome"
  | some (.ok (.abrupt outcome)) =>
      let final ← Transactions.finishFrame initial outcome
      let events ← final.world.events.mapM fun event => do
        let entry ← EventObservation.encode final.world.thisAddress root.events event
        return { event with rawLog := some entry }
      return some { final with world := { final.world with events } }

/-- Execute a selected root without falling back to a bounded model or another name. -/
def execute (slice : ObservedImport.Slice) (name : String) (oracle : DenoteOracle)
    (fuel : Nat) (world : Verity.ContractState) (args : List Nat) :
    Except String (Option Transactions.FrameResult) := do
  executeRoot (← findRoot slice name) oracle fuel world args

end Compiler.CompilationModel.SolidityImport.ObservedExecution
