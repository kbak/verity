import Compiler.SolidityImport.Import

/-! Same-frame scalar-result helpers and storage for the observed loop backend.
The bounded-model backend remains separate. Aggregate results,
external calls and helper calls nested in larger expressions remain separate work. -/

namespace Compiler.CompilationModel.SolidityImport.ObservedImport
open Lean ControlFlow

private abbrev Results := Array (String × String)

/-- Restore a caller's lexical bindings while retaining discovered layouts and fresh names. -/
private def restore (saved : Env) : M Unit :=
  modify fun e => { e with
    values := saved.values, writableLocals := saved.writableLocals
    paths := saved.paths, storageMappingVars := saved.storageMappingVars
    fixedStructArrayVars := saved.fixedStructArrayVars, snapshots := saved.snapshots
    mems := saved.mems, flatStructs := saved.flatStructs, abiElements := saved.abiElements
    calldataBytes := saved.calldataBytes, scalarArrays := saved.scalarArrays
    byteBuffers := saved.byteBuffers, stringBuffers := saved.stringBuffers
    storageBytesVars := saved.storageBytesVars
    storageDynamicArrayVars := saved.storageDynamicArrayVars
    fnPtrs := saved.fnPtrs, scalarTy := saved.scalarTy, enumBounds := saved.enumBounds
    zeroInitLocals := saved.zeroInitLocals, legacyCleanParams := saved.legacyCleanParams
    yulNames := saved.yulNames, yulMemoryArrays := saved.yulMemoryArrays
    yulMemoryStructs := saved.yulMemoryStructs, bodyAssigned := saved.bodyAssigned
    stack := saved.stack, currentFile := saved.currentFile, unchecked := saved.unchecked
    helperResult := saved.helperResult, helperReturnId := saved.helperReturnId
    multiHelperResults := saved.multiHelperResults
    flatStructHelperResult := saved.flatStructHelperResult
    helperPost := saved.helperPost, rootReturns := saved.rootReturns
    rootReturnTypes := saved.rootReturnTypes, rootIsVoid := saved.rootIsVoid
    rootPost := saved.rootPost }

private def replace (node : Json) (key : String) (value : Json) : Json :=
  node.setObjVal! key value

private def helperCall (node : Json) : M Bool := do
  unless optStr node "nodeType" == some "FunctionCall" &&
      optStr node "kind" == some "functionCall" do return false
  let callee := (field? node "expression").getD Json.null
  let id := (field? callee "referencedDeclaration").bind (·.getNat?.toOption)
  return id.any (← get).funs.contains

/-- A captured helper result remains a typed scalar identifier to the ordinary leaf lowerer. -/
private def resultNode (call : Json) (name : String) : M Json := do
  let id ← mNat (← mField call "id")
  let some ty := paramType (← mType call) | failAt call "observed helper result must be scalar"
  modify fun e => { e with
    values := e.values.insert id (.localVar name), scalarTy := e.scalarTy.insert id ty }
  return Json.mkObj [("nodeType", toJson "Identifier"), ("id", toJson id),
    ("referencedDeclaration", toJson id), ("name", toJson name),
    ("typeDescriptions", ← mField call "typeDescriptions"), ("src", ← mField call "src")]

/-- A local return boundary leaves modifier post-code in the enclosing continuation.
Source reverts/INVALID still abort the entire frame, bypassing all post-code. -/
private def withModifiers (mods : Array Json) (results : List String)
    (body : M ControlLowering.Body) : M ControlLowering.Body := do
  if mods.isEmpty then return ← body
  let (pre, post) ← ObservedSupport.modifiers mods
  let code ← body
  let name ← fresh
  return pre.toList.map Program.atom ++ [.call name results code] ++
    post.toList.map Program.atom

mutual
private partial def lowerBody (node : Json) (results : Option Results) : M ControlLowering.Body :=
  ControlLowering.lower ObservedSupport.expression ObservedSupport.statement node 0
    (special results)

private partial def inlineCall (call : Json) : M (ControlLowering.Body × Option String) := do
  let (id, args) ← ObservedSupport.resolveCall call
  let saved ← get
  if saved.stack.contains id then failAt call "recursive observed helper call"
  let some fn := saved.funs.find? id | failAt call "unresolved observed helper"
  unless [some "internal", some "private", some "public"].contains (optStr fn "visibility") do
    failAt call "observed helpers require same-frame calls"
  let mods ← mArr (← mField fn "modifiers")
  let body ← mField fn "body"
  unless !body.isNull do failAt fn "observed helper has no body"
  let params ← mArr (← mField (← mField fn "parameters") "parameters")
  unless params.size == args.size do failAt call "observed helper argument count differs"
  let returns ← mArr (← mField (← mField fn "returnParameters") "parameters")
  unless returns.size <= 1 do failAt fn "observed helpers require scalar or void results"
  modify fun e => { e with
    stack := id :: saved.stack, currentFile := saved.nodeFile.find? id |>.getD saved.currentFile
    unchecked := true, bodyAssigned := bodyAssignedIds body, zeroInitLocals := #[] }
  validateLegacyDeclaration fn false #[] .observed
  let (pre, yul) ← ObservedSupport.bindHelper params args body call saved.yulNames
  modify fun e => { e with yulNames := yul }
  noteFn fn
  let mut results : Results := #[]
  let mut initial := pre
  for result in returns do
    let ty ← mType result
    let some scalar := paramType ty | failAt result "observed helper result must be scalar"
    let sourceName := (optStr result "name").getD ""
    let binding ← freshFor (if sourceName == "" then "result" else sourceName)
    let rid ← mNat (← mField result "id")
    results := results.push (binding, ty)
    initial := initial.push (.letVar binding (.literal 0))
    modify fun e => { e with
      values := e.values.insert rid (.localVar binding)
      writableLocals := e.writableLocals.insert rid binding
      scalarTy := e.scalarTy.insert rid scalar }
  let name ← fresh
  let code ← withModifiers mods (results.toList.map Prod.fst) (lowerBody body (some results))
  restore saved
  return (initial.toList.map Program.atom ++
    [.call name (results.toList.map Prod.fst) code], results[0]?.map Prod.fst)

private partial def value (node : Json) : M (ControlLowering.Body × Json) := do
  if ← helperCall node then
    let (pre, result) ← inlineCall node
    let some binding := result | failAt node "void helper used as a value"
    return (pre, ← resultNode node binding)
  return ([], node)

private partial def special (results : Option Results) (node : Json) (_depth : Nat) :
    M (Option ControlLowering.Body) := do
  let kind ← mKind node
  if kind == "Return" then
    let expression := (field? node "expression").getD Json.null
    if let some bindings := results then
      if expression.isNull then return some [.leaveCall]
      let components ← if bindings.size == 1 then pure #[expression]
        else ObservedSupport.returnComponents expression
      unless components.size == bindings.size do failAt node "observed return arity mismatch"
      let mut pre : ControlLowering.Body := []
      let mut assignments : ControlLowering.Body := []
      for ((binding, ty), component) in bindings.zip components do
        let (before, replacement) ← value component
        let lowered ← ObservedSupport.expression replacement
        let converted ← ObservedSupport.cast ty (← mType replacement) lowered replacement
        let captured ← fresh
        pre := pre ++ before ++ converted.pre.toList.map Program.atom ++
          [.atom (.letVar captured converted.expr)]
        assignments := assignments ++ [.atom (.assignVar binding (.localVar captured))]
      return some (pre ++ assignments ++ [.leaveCall])
    if !expression.isNull && (← helperCall expression) then
      let (pre, replacement) ← value expression
      let tail ← ObservedSupport.statement (replace node "expression" replacement)
      return some (pre ++ tail.toList.map Program.atom)
  if kind == "VariableDeclarationStatement" then
    let expression := (field? node "initialValue").getD Json.null
    if ← helperCall expression then
      let declarations ← mArr (← mField node "declarations")
      unless declarations.size == 1 && !declarations[0]!.isNull &&
          (paramType (← mType declarations[0]!)).isSome do
        failAt node "observed helper binding requires one scalar local"
      let (pre, replacement) ← value expression
      let tail ← ObservedSupport.statement (replace node "initialValue" replacement)
      return some (pre ++ tail.toList.map Program.atom)
  if kind == "ExpressionStatement" then
    let expression ← mField node "expression"
    if ← helperCall expression then return some (← inlineCall expression).1
    if optStr expression "nodeType" == some "Assignment" then
      let right ← mField expression "rightHandSide"
      if ← helperCall right then
        unless optStr expression "operator" == some "=" &&
            optStr (← mField expression "leftHandSide") "nodeType" == some "Identifier" do
          failAt expression "observed helper assignment requires a simple identifier target"
        let (pre, replacement) ← value right
        let tail ← ObservedSupport.statement
          (replace node "expression" (replace expression "rightHandSide" replacement))
        return some (pre ++ tail.toList.map Program.atom)
  return none
end

/-- Observed scalar ABI with storage and same-frame scalar-result helpers.
The caller supplies compiler-indexed declarations and storage layout. -/
structure Root where
  control : ObservedControlRoot
  fields : List Field

/-- Lower general loops with storage effects and explicit helper return boundaries. -/
def lowerRoot (fn : Json) : M Root := do
  let frame ← prepareObservedControlRoot fn
  noteFn fn
  let mods ← mArr (← mField fn "modifiers")
  let env ← get
  let mut results : Results := #[]
  for (expr, ty) in env.rootReturns.zip env.rootReturnTypes do
    let .localVar name := expr | failAt fn "observed result requires a named binding"
    results := results.push (name, ty)
  let body ← withModifiers mods (results.toList.map Prod.fst)
    (lowerBody (← mField fn "body") (if mods.isEmpty then none else some results))
  LegacyStructs.validateClosure
  let fields ← observedStorageFields
  return {
    control := {
      params := frame.params
      body := frame.initial.toList.map Program.atom ++ body ++ [.atom frame.finish] }
    fields }

/-- One selected root in an observed import. No bounded-model coverage is asserted. -/
structure Function where
  name : String
  root : Root

/-- Named observed roots with the compiler-derived storage layout. -/
structure Slice where
  functions : List Function

/-- Import observed roots through the ordinary compiler/source/deployment pipeline. -/
def importSlice (pkgRoot projectRoot : System.FilePath) (entry contract : String)
    (roots : Array (String × Array String)) (profile : Profile) :
    Lean.MetaM (Slice × ImportReport) := do
  let prepared ← prepareImportSlice pkgRoot projectRoot entry contract profile
  unless prepared.legacy && !profile.sourceGas do
    throwError "observed imports require Solidity 0.7.6 without source-gas instrumentation"
  let mut env := prepared.env
  let mut functions : Array Function := #[]
  let mut ids : Array Nat := #[]
  let mut signatures : Array Json := #[]
  for (name, written) in roots do
    let (fn, types) ← (selectImportRoot contract name written).run' env
    let id ← (do mNat (← mField fn "id")).run' env
    if ids.contains id then throwError "function {contract}.{name} is imported twice"
    if functions.any (·.name == name) then
      throwError "root function name collision: {contract}.{name}; import overloads separately"
    ids := ids.push id
    signatures := signatures.push (Json.mkObj
      [("function", toJson name), ("parameterTypes", toJson types)])
    env := resetImportRoot env (env.nodeFile.find? id |>.getD entry)
    let (root, next) ← (lowerRoot fn).run env
    env := next
    functions := functions.push { name, root }
  let fields ← observedStorageFields.run' env
  let imported := functions.toList.map fun f => { f with root := { f.root with fields } }
  let statuses := imported.map fun f =>
    { function := f.name, denoteCovered := false,
      compilerProof := .unavailable
        "observed control only; no bounded-model coverage or frontend/codegen refinement" :
      FunctionStatus }
  let report ← finishImportReport pkgRoot contract roots profile prepared env signatures statuses
    (backend := "observed-canonical-scalar") (extraSources := #[
      "Compiler/SolidityImport/LoopExecution.lean", "Compiler/SolidityImport/ControlFlow.lean",
      "Compiler/SolidityImport/ControlLowering.lean", "Compiler/SolidityImport/ControlDenote.lean",
      "Compiler/SolidityImport/ControlCodegen.lean", "Compiler/SolidityImport/ObservedImport.lean",
      "Compiler/SolidityImport/ObservedCommand.lean", "Compiler/SolidityImport/LegacyStructs.lean",
      "Compiler/SolidityImport/TupleReturns.lean", "Compiler/SolidityImport/TypesAndRecords.lean"])
  return ({ functions := imported }, report)

end Compiler.CompilationModel.SolidityImport.ObservedImport
