import Compiler.SolidityImport.SignatureMocks
import Mathlib.Tactic.SplitIfs

/-! Independent finite programs for metered static-call tests. Constant-response
runtimes push a word, MSTORE at zero and RETURN/REVERT a fixed length. GAS-response
runtimes use GAS instead of the word push. INVALID and forbidden SSTORE halt
exceptionally. Recovery results come from the independent Python oracle, never EVM. -/
namespace Contracts.SolidityImportSmoke.StaticGasMocks
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport Denote ByteExternalCall

/-- A configured fixed-runtime child, whose code is checked by the EVM harness. -/
structure Child where
  address : Nat
  word : Nat
  length : Nat
  mode : String

/-- Independent runtime cost including expansion from empty child memory. -/
def cost (child : Child) : Nat :=
  let words := (max 32 child.length + 31) / 32
  (if child.mode == "gas" then 14 else 15) + 3 * words + words * words / 512

/-- Static success preserves the entire world; exceptional exits have no world. -/
def respond (child : Child) (request : Request) (world : Verity.ContractState) :
    Response Verity.ContractState Verity.StorageKey :=
  if child.mode == "exceptional" || request.gas < cost child then .exceptional []
  else
    let value := if child.mode == "gas" then request.gas - 2 else child.word
    let data := (wordBytes value ++ List.replicate child.length 0).take child.length
    if child.mode == "revert" then .revert data [] else .success world data []

/-- Static calls only, with exact recovery input rows and explicit fixed children.
The base environment also supports the existing independent hash-validator model. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let base ← SignatureMocks.configure input
  let some original := base.adversary | throw "static gas oracle missing"
  let children ← (← (← input.getObjVal? "staticGasChildren").getArr?).toList.mapM fun j => do
    let child : Child := {
      address := ← (← j.getObjVal? "address").getNat?
      word := ← (← j.getObjVal? "word").getNat?
      length := ← (← j.getObjVal? "length").getNat?
      mode := ← (← j.getObjVal? "mode").getStr? }
    unless 256 < child.address && child.address < 2^160 && child.word < 2^256 &&
        child.length ≤ 255 && ["return", "revert", "gas", "exceptional"].contains child.mode do
      throw "invalid static gas child"
    pure child
  unless (children.map Child.address).eraseDups.length == children.length do
    throw "duplicate static gas child"
  return { base with adversary := some {
    accepts := fun request world =>
      request.kind == .staticcall && request.value == 0 &&
        (children.any (·.address == request.target) || original.accepts request world)
    respond := fun request world =>
      if request.target == 1 && request.gas < 3000 then .exceptional []
      else match children.find? (·.address == request.target) with
        | some child => respond child request world
        | none => original.respond request world
    valid := by
      intro request world
      split
      · trivial
      · split
        · rename_i child _
          unfold respond
          split_ifs <;> simp [Response.valid]
        · exact original.valid request world } }

end Contracts.SolidityImportSmoke.StaticGasMocks
