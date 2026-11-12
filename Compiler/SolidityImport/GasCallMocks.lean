import Verity.Core.Model.Denote
import Lean.Data.Json

/-! Independent fixed bytecode child for gas-observation validation. The complete
runtime is GAS PUSH1(0) MSTORE PUSH1(32) PUSH1(0) RETURN/REVERT: 17 gas, including
memory expansion; INVALID consumes the whole allowance. These are explicit test
programs, not inferred foreign-contract behavior. -/
namespace Compiler.CompilationModel.SolidityImport.GasCallMocks
open Denote ByteExternalCall

private def respond (returns reverts invalid empty : Nat) (request : Request)
    (world : Verity.ContractState) : Response Verity.ContractState Verity.StorageKey :=
  if request.kind = .staticcall then .revert [] []
  else if request.target == empty then .success world [] []
  else if request.target == invalid || request.gas < 17 then .exceptional []
  else if request.target == returns then .success world (wordBytes (request.gas - 2)) []
  else if request.target == reverts then .revert (wordBytes (request.gas - 2)) []
  else .exceptional []

/-- Explicit test world; it supplies no source gas or default allowance. -/
def environment (returns reverts invalid empty : Nat) : ByteCallEnvironment :=
  { adversary := some {
      accepts := fun request _ =>
        (request.kind == .call || request.kind == .delegatecall) &&
        [returns, reverts, invalid, empty].contains request.target
      respond := respond returns reverts invalid empty
      valid := by
        intro request world
        by_cases h : request.kind = .staticcall
        · simp [respond, h, Response.valid]
        · cases respond returns reverts invalid empty request world <;> simp [Response.valid, h] } }

/-- The fixed test accounts are chosen by the harness and checked against code. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "gasChildren"
  let values ← (← config.getArr?).toList.mapM Lean.Json.getNat?
  let [returns, reverts, invalid, empty] := values | throw "expected four gas child addresses"
  unless values.eraseDups.length == 4 && values.all (fun n => 256 < n && n < 2^160) do
    throw "invalid gas child addresses"
  return environment returns reverts invalid empty

end Compiler.CompilationModel.SolidityImport.GasCallMocks
