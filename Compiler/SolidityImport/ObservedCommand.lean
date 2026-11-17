import Compiler.SolidityImport.ObservedImport

/-! Explicit observed mode for the ordinary Solidity import command. It uses the
same checked source pipeline, but emits an observed slice rather than a bounded
CompilationModel or a coverage theorem. Canonical scalar ABI is the current scope. -/

open Lean Meta Elab Command

namespace Compiler.CompilationModel.SolidityImport

private partial def quoteControl (body : ControlLowering.Body) : CommandElabM Term := do
  let items ← body.toArray.mapM fun statement => do
    match statement with
    | .atom stmt => `(ControlFlow.Program.atom $(← quoteStmt stmt))
    | .branch pre condition yes no =>
        let pre ← pre.toArray.mapM quoteStmt
        `(ControlFlow.Program.branch [$pre,*] $(← quoteExpr condition)
          $(← quoteControl yes) $(← quoteControl no))
    | .loop pre condition body post =>
        let pre ← pre.toArray.mapM quoteStmt
        `(ControlFlow.Program.loop [$pre,*] $(← quoteExpr condition)
          $(← quoteControl body) $(← quoteControl post))
    | .breakLoop => `(ControlFlow.Program.breakLoop)
    | .continueLoop => `(ControlFlow.Program.continueLoop)
    | .call name results body =>
        `(ControlFlow.Program.call $(quote name) $(quote results) $(← quoteControl body))
    | .leaveCall => `(ControlFlow.Program.leaveCall)
  `([$items,*])

private def quoteObserved (slice : ObservedImport.Slice) : CommandElabM Term := do
  let functions ← slice.functions.toArray.mapM fun fn => do
    let params ← fn.root.control.params.toArray.mapM fun p => do
      `(Compiler.CompilationModel.Param.mk $(quote p.name) $(← quoteParamType p.ty))
    let fields ← fn.root.fields.toArray.mapM quoteField
    `(({ name := $(quote fn.name), root := {
        control := { params := [$params,*], body := $(← quoteControl fn.root.control.body) }
        fields := [$fields,*] } } : ObservedImport.Function))
  `(({ functions := [$functions,*] } : ObservedImport.Slice))

/-- Select the observed backend explicitly; bounded imports keep their existing syntax. -/
syntax (name := solidityObservedImportCmd)
  "solidity_import " ident &"from" str &"entry" str " using " term:max
  &"observed" &"contract" ident (ppLine solidityRoot)+ : command

/-- Elaborate a compiler-checked observed slice, provenance and explicit scope. -/
@[command_elab solidityObservedImportCmd]
def elabSolidityObservedImport : CommandElab := fun stx => do
  let `(solidity_import $alias from $root entry $entry using $prof observed contract $contract
      $roots:solidityRoot*) := stx | throwUnsupportedSyntax
  let saved ← getEnv
  let errors := ((← get).messages.toList.filter (·.severity == .error)).length
  try
    if debug.skipKernelTC.get (← getOptions) then
      throwError "kernel checking must be enabled"
    let profile ← liftTermElabM <| readImportProfile prof
    let roots ← roots.mapM fun root => do
      let `(solidityRoot| function $fn ( $tys,* )) := root | throwUnsupportedSyntax
      pure (fn.getId.toString (escape := false),
        tys.getElems.map (·.getId.toString (escape := false)))
    let pkg ← importPackageRoot
    let project := if root.getString.startsWith "/" then
      System.FilePath.mk root.getString else pkg / root.getString
    let (slice, report) ← liftTermElabM <| ObservedImport.importSlice pkg project entry.getString
      (contract.getId.toString (escape := false)) roots profile
    let ns := (← getCurrNamespace) ++ alias.getId
    let name (suffix : Name) := mkIdent (`_root_ ++ ns ++ suffix)
    elabCommand (← `(set_option maxRecDepth 16384 in
      def $(name `observed) : ObservedImport.Slice := $(← quoteObserved slice)))
    elabCommand (← `(set_option maxRecDepth 16384 in
      def $(name `report) : ImportReport := $(← quoteReport report)))
    elabCommand (← `(def $(name `sourceDigest) : String := $(quote report.sourceDigest)))
    elabCommand (← `(def $(name `scope) : String :=
      "observed canonical scalar ABI; exhaustion is no observation; no refinement theorem"))
    if ((← get).messages.toList.filter (·.severity == .error)).length > errors then
      throwError "observed Solidity import failed to check"
  catch e =>
    setEnv saved
    throw e

end Compiler.CompilationModel.SolidityImport
