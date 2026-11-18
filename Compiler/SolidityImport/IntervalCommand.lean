import Compiler.SolidityImport.Import
import Compiler.SolidityImport.CertifiedInterval
import Compiler.SolidityImport.RecordSnapshot

/-! Extract one checked source iteration for a dependent proof of progress. -/

open Lean Meta Elab Command

namespace Compiler.CompilationModel.SolidityImport

/-- Extract the first lowering instance of an exact AST source site reached from this root.
No enclosing function model or successful finite loop is constructed by extraction. -/
def importIntervalSite (pkg project : System.FilePath) (entry contract functionName : String)
    (types : Array String) (profile : Profile) (file : String) (line column : Nat) :
    MetaM CertifiedInterval.Site := do
  let prepared ← prepareImportSlice pkg project entry contract profile
  unless prepared.legacy do throwError "conditional interval import requires Solidity 0.7.6"
  let (fn, resolved) ← (selectImportRoot contract functionName types).run' prepared.env
  if profile.legacyDivisionHalt && optStr fn "stateMutability" != some "pure" then
    throwError "legacyDivisionHalt requires pure function roots"
  let some bytes := prepared.env.files.find? file | throwError "unknown loop source unit {file}"
  let mut current := (1, 1)
  let mut offset := 0
  for byte in bytes.data do
    if current == (line, column) then break
    current := if byte == 10 then (current.1 + 1, 1) else (current.1, current.2 + 1)
    offset := offset + 1
  unless current == (line, column) do throwError "loop position is outside {file}"
  let rootId ← flexNat (← field fn "id")
  let rootFile := (prepared.env.nodeFile.find? rootId).getD entry
  let frame := resetImportRoot prepared.env rootFile
  let c ← IntervalCapture.firstInstance file offset ((visitIntervalRoot fn).run' frame)
  let e := c.after
  let iteration := c.iteration
  unless executableStmtListCovered iteration.body do
    (failAt c.node "interval iteration contains a statement outside denotation coverage").run' e
  let accesses := e.memoryAccesses.extract c.before.memoryAccesses.size e.memoryAccesses.size
  (MemoryBounds.validate iteration.body.toArray).run' { e with memoryAccesses := accesses }
  let callees := e.included.filterMap fun fn =>
    e.funs.find? fn.declId <|> e.modifiers.find? fn.declId
  let bodies := #[c.node] ++ callees
  (LegacyStructs.validateBodies bodies).run' e
  let frame := { c.before with fieldsByName := e.fieldsByName }
  let snapshots ← (RecordSnapshot.check c.node iteration.body frame).run' e
  for key in ["parameters", "returnParameters"] do
    (validateLegacyDeclaration (← field fn key)).run' prepared.env
  (validateLegacyDeclaration c.node false #[] .bounded false snapshots.assignments).run' e
  for callee in callees do (validateLegacyDeclaration callee).run' e
  let fields ← observedStorageFields.run' e
  let src ← str (← field c.node "src")
  let root := s!"{contract}.{functionName}({String.intercalate "," resolved.toList})"
  let stack := c.before.stack.reverse
  let signature : Json := Json.mkObj [("root", .str root), ("file", .str file),
    ("range", .str src), ("frames", toJson stack), ("solcSha256", .str prepared.solcSha256),
    ("allocation", toJson c.before.next)]
  let sources := #["Compiler/SolidityImport/IntervalSite.lean",
    "Compiler/SolidityImport/IntervalCapture.lean",
    "Compiler/SolidityImport/RecordSnapshot.lean",
    "Compiler/CompilationModel/ValidationHelpers.lean",
    "Compiler/SolidityImport/CertifiedInterval.lean",
    "Compiler/SolidityImport/IntervalCommand.lean",
    "Compiler/SolidityImport/IntervalSearchProofs.lean",
    "Compiler/SolidityImport/LoopExecution.lean"]
  let report ← finishImportReport pkg contract #[(functionName, resolved)] profile prepared
    e #[signature] [] #[] "interval-first-instance" sources
  return {
    sourceDigest := report.sourceDigest, root, file, sourceRange := src, callStack := stack,
    frameAllocation := c.before.next, locals := c.before.values.toList,
    structLocals := c.before.flatStructs.toList.map fun (id, obj) => (id, obj.members.toList),
    arrayBases := c.before.fixedStructArrayVars.toList.map fun (id, a) =>
      (id, a.slot, a.length, a.wordCount),
    inputs := IntervalSearch.entryInputs c.before.bound iteration.body, bits := iteration.bits,
    lowName := iteration.lowName, highName := iteration.highName, midName := iteration.midName,
    doneName := c.doneName, snapshotRecords := snapshots.destinations.toList.mergeSort,
    nonzeroInputs := snapshots.nonzero,
    fields, body := iteration.body }

private def quoteIntervalSite (p : CertifiedInterval.Site) : CommandElabM Term := do
  let locals ← p.locals.toArray.mapM fun (id, expr) => do `(($(quote id), $(← quoteExpr expr)))
  let bases ← p.arrayBases.toArray.mapM fun (id, expr, length, words) => do
    `(($(quote id), $(← quoteExpr expr), $(quote length), $(quote words)))
  let fields ← p.fields.toArray.mapM quoteField
  let body ← p.body.toArray.mapM quoteStmt
  `(({ sourceDigest := $(quote p.sourceDigest), root := $(quote p.root), file := $(quote p.file),
       sourceRange := $(quote p.sourceRange), callStack := $(quote p.callStack),
       frameAllocation := $(quote p.frameAllocation), locals := [$locals,*],
       structLocals := $(quote p.structLocals), arrayBases := [$bases,*],
       snapshotRecords := $(quote p.snapshotRecords), nonzeroInputs := $(quote p.nonzeroInputs),
       inputs := $(quote p.inputs), bits := $(quote p.bits),
       lowName := $(quote p.lowName), highName := $(quote p.highName),
       midName := $(quote p.midName), doneName := $(quote p.doneName),
       fields := [$fields,*], body := [$body,*] } : CertifiedInterval.Site))

/-- Extract the first specialized lowering instance of this exact loop in the selected root. -/
syntax (name := solidityIntervalImportCmd)
  "solidity_import " ident &"from" str &"entry" str " using " term:max
  &"interval" &"contract" ident ppLine solidityRoot
  ppLine &"loop" str &"line" num &"column" num : command

/-- Publish the source-selected iteration. Total evaluation requires a typed progress proof
and proof that the initial lexical state belongs to its domain. -/
@[command_elab solidityIntervalImportCmd]
def elabSolidityIntervalImport : CommandElab := fun stx => do
  let `(solidity_import $alias from $root entry $entry using $prof interval contract $contract
      $selected:solidityRoot loop $file line $line column $column) := stx | throwUnsupportedSyntax
  let `(solidityRoot| function $fn ( $tys,* )) := selected | throwUnsupportedSyntax
  if debug.skipKernelTC.get (← getOptions) then throwError "kernel checking must be enabled"
  let profile ← liftTermElabM <| readImportProfile prof
  let pkg ← importPackageRoot
  let project := if root.getString.startsWith "/" then System.FilePath.mk root.getString
    else pkg / root.getString
  let site ← liftTermElabM <| importIntervalSite pkg project entry.getString
    (contract.getId.toString (escape := false)) (fn.getId.toString (escape := false))
    (tys.getElems.map (·.getId.toString (escape := false))) profile file.getString
    line.getNat column.getNat
  let name := mkIdent (`_root_ ++ (← getCurrNamespace) ++ alias.getId ++ `site)
  let saved ← getEnv
  let errors := ((← get).messages.toList.filter (·.severity == .error)).length
  try
    elabCommand (← `(set_option maxRecDepth 16384 in
      def $name : CertifiedInterval.Site := $(← quoteIntervalSite site)))
    if ((← get).messages.toList.filter (·.severity == .error)).length > errors then
      throwError "conditional interval site failed to check"
  catch error =>
    setEnv saved
    throw error

end Compiler.CompilationModel.SolidityImport
