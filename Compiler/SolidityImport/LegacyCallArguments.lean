import Compiler.SolidityImport.ExprHelpers

/-!
A deliberately small commuting-argument boundary for legacy internal calls.
Solidity does not specify sibling evaluation order. One direct unsigned postfix
increment commutes with distinct scalar identifiers/literals and at most one
calldata byte identifier (including its memory conversion). No arbitrary helper,
reference path, allocation expression or sibling read of the target is admitted.
-/

namespace Compiler.CompilationModel.SolidityImport
open Lean

private def declarationId? (j : Json) : Option Nat :=
  (field? j "referencedDeclaration").bind (fun id => id.getNat?.toOption)

private def nodeTypeString (j : Json) : String :=
  ((field? j "typeDescriptions").bind (fun t => optStr t "typeString")).getD ""

private def postIncrementTarget? (j : Json) (env : Env) : Option Nat := do
  guard (optStr j "nodeType" == some "UnaryOperation")
  guard (optStr j "operator" == some "++")
  guard ((field? j "prefix").bind (fun b => b.getBool?.toOption) == some false)
  let target ← field? j "subExpression"
  guard (optStr target "nodeType" == some "Identifier")
  let ty := nodeTypeString target
  guard (ty.startsWith "uint" && (bitsOf ty).isSome)
  let id ← declarationId? target
  guard (env.writableLocals.contains id || env.stateVars.contains id)
  return id

private def independentScalar (j : Json) (target : Nat) (env : Env) : Bool :=
  if optStr j "nodeType" == some "Literal" then
    [some "number", some "bool"].contains (optStr j "kind")
  else if optStr j "nodeType" == some "Identifier" then
    match declarationId? j with
    | some id =>
        id != target && (localParamType (nodeTypeString j)).isSome &&
          (env.stateVars.contains id || env.numericConstants.contains id ||
            match env.values.find? id with
            | some (.literal _) | some (.param _) | some (.localVar _) => true
            | _ => false)
    | none => false
  else false

/-- Admit exactly one direct legacy unsigned postfix increment with independent
siblings. Existing lowering captures the old value, writes once, then enters the
helper. A single calldata descriptor may be forwarded or copied to memory; it
cannot alias the scalar target. General effect ordering remains rejected. -/
def independentLegacyPostIncrementArgs (nodes : Array Json) (env : Env) : Bool := Id.run do
  if !env.legacyWrapping then return false
  let increments := nodes.filterMap (fun node => postIncrementTarget? node env)
  if increments.size != 1 then return false
  let target := increments[0]!
  let mut buffers := 0
  for node in nodes do
    if (postIncrementTarget? node env).isSome then continue
    if independentScalar node target env then continue
    if optStr node "nodeType" != some "Identifier" then return false
    if nodeTypeString node != "bytes calldata" then return false
    let some id := declarationId? node | return false
    let some buffer := env.calldataBytes.find? id | return false
    if id == target || buffer.inMemory then return false
    buffers := buffers + 1
    if buffers > 1 then return false
  return true

end Compiler.CompilationModel.SolidityImport
