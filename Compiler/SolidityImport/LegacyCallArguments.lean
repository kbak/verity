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

/-- Detect direct and transitively inlined source gas observations. Visited
function IDs bound recursion; an ordinary view helper may still observe GAS. -/
partial def containsSourceGasRead (node : Json) (env : Env) (seen : List Nat := []) : Bool :=
  match node with
  | .arr nodes => nodes.any (fun child => containsSourceGasRead child env seen)
  | .obj fields =>
      let callee := (field? node "expression").getD Json.null
      let id := (field? callee "referencedDeclaration").bind (·.getInt?.toOption)
      let direct := optStr node "nodeType" == some "FunctionCall" &&
        optStr callee "name" == some "gasleft" && id.any (· < 0)
      let nested := if optStr node "nodeType" == some "FunctionCall" then
        match id with
        | some id => if id < 0 then false else
          let target := resolveInContracts env env.linearizedBases.toList id.toNat
            |>.getD id.toNat
          if seen.contains target then false else
            (env.funs.find? target).any (fun fn => containsSourceGasRead fn env (target :: seen))
        | none => false
        else false
      direct || nested || fields.foldl
        (fun found _ child => found || containsSourceGasRead child env seen) false
  | _ => false

private partial def containsCall (node : Json) : Bool :=
  match node with
  | .arr nodes => nodes.any containsCall
  | .obj fields => optStr node "nodeType" == some "FunctionCall" ||
      fields.foldl (fun found _ child => found || containsCall child) false
  | _ => false

/-- Count gas reads in a scalar expression with no other effects. Call siblings
are restricted below, so changing their evaluation order cannot change values;
the original-bytecode meter still charges their actual instruction costs. -/
private partial def sourceGasReads? (node : Json) (env : Env) : Option Nat := do
  match optStr node "nodeType" with
  | some "Identifier" =>
      let id ← declarationId? node
      guard ((localParamType (nodeTypeString node)).isSome || env.enumBounds.contains id)
      guard (env.values.contains id || env.stateVars.contains id ||
        env.numericConstants.contains id)
      pure 0
  | some "Literal" =>
      guard ([some "number", some "bool"].contains (optStr node "kind"))
      pure 0
  | some "FunctionCall" =>
      let callee ← field? node "expression"
      let id ← (field? callee "referencedDeclaration").bind (·.getInt?.toOption)
      let args ← (field? node "arguments").bind (·.getArr?.toOption)
      if id < 0 then
        guard (optStr callee "nodeType" == some "Identifier" &&
          optStr callee "name" == some "gasleft" && args.isEmpty)
        pure 1
      else
        let fn ← env.funs.find? id.toNat
        guard (optStr fn "stateMutability" == some "pure")
        guard ((field? fn "virtual").bind (·.getBool?.toOption) != some true)
        let modifiers ← (field? fn "modifiers").bind (·.getArr?.toOption)
        guard modifiers.isEmpty
        let params ← ((field? fn "parameters").bind (field? · "parameters")).bind
          (·.getArr?.toOption)
        let outputs ← ((field? fn "returnParameters").bind (field? · "parameters")).bind
          (·.getArr?.toOption)
        guard (outputs.size == 1 && (localParamType (nodeTypeString outputs[0]!)).isSome)
        let statements ← ((field? fn "body").bind (field? · "statements")).bind
          (·.getArr?.toOption)
        guard (statements.size == 1 && optStr statements[0]! "nodeType" == some "Return")
        let result ← field? statements[0]! "expression"
        guard (!containsCall result)
        let mut helper := env
        for param in params do
          guard ((localParamType (nodeTypeString param)).isSome)
          let pid ← (field? param "id").bind (·.getNat?.toOption)
          helper := { helper with values := helper.values.insert pid (.localVar "") }
        guard (sourceGasReads? result helper == some 0)
        let mut reads := 0
        if optStr callee "nodeType" == some "MemberAccess" then
          let receiver ← field? callee "expression"
          if (localParamType (nodeTypeString receiver)).isSome then
            reads := reads + (← sourceGasReads? receiver env)
        for arg in args do reads := reads + (← sourceGasReads? arg env)
        pure reads
  | some "BinaryOperation" =>
      let left ← sourceGasReads? (← field? node "leftExpression") env
      let right ← sourceGasReads? (← field? node "rightExpression") env
      pure (left + right)
  | some "TupleExpression" =>
      let parts ← (field? node "components").bind (·.getArr?.toOption)
      guard (parts.size == 1)
      sourceGasReads? parts[0]! env
  | some "Conditional" =>
      let condition ← sourceGasReads? (← field? node "condition") env
      let yes ← sourceGasReads? (← field? node "trueExpression") env
      let no ← sourceGasReads? (← field? node "falseExpression") env
      pure (condition + yes + no)
  | _ => none

/-- One source GAS read with independent scalar/byte identifiers. One immutable
calldata buffer may be copied to fresh memory: the copy and source-evidence read
have disjoint effects, while the original meter charges the actual copy position.
Other allocation expressions, increments and competing gas reads stay rejected. -/
def independentSourceGasArgs (nodes : Array Json) (env : Env) : Bool := Id.run do
  if !env.legacyWrapping || !env.sourceGas then return false
  let mut reads := 0
  let mut copies := 0
  for node in nodes do
    if optStr node "nodeType" == some "Identifier" && nodeTypeString node == "bytes memory" then
      let some id := declarationId? node | return false
      if !env.byteBuffers.contains id then return false
    else if optStr node "nodeType" == some "Identifier" &&
        nodeTypeString node == "bytes calldata" then
      let some id := declarationId? node | return false
      let some buffer := env.calldataBytes.find? id | return false
      if buffer.inMemory then return false
      copies := copies + 1
      if copies > 1 then return false
    else
      let some count := sourceGasReads? node env | return false
      reads := reads + count
  return reads == 1

end Compiler.CompilationModel.SolidityImport
