import Compiler.SolidityImport.Import
import Compiler.SolidityImport.ObservedExecution
import Compiler.SolidityImport.ControlCodegen
import Compiler.SolidityImport.Differential

/-! Test-only typed-AST entry to the observed scalar-control lowering API.
Arguments are canonical scalar ABI words; dispatch and arbitrary ABI validation
are not asserted by these component checks. -/

open Lean Elab Command Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport

/-- Deliberate typed-control faults, shared by the observer and generated route.
These are control-IR sensitivity checks, not importer-source mutation coverage. -/
private partial def perturb (mutation : String) (body : ControlLowering.Body) :
    ControlLowering.Body := body.map fun statement =>
  match statement with
  | .continueLoop => if mutation == "continue-exits" then .breakLoop else statement
  | .breakLoop => if mutation == "break-repeats" then .continueLoop else statement
  | .branch pre cond yes no => .branch pre cond (perturb mutation yes) (perturb mutation no)
  | .loop pre cond loopBody post =>
      let condition := if mutation == "inclusive-bound" then
          match cond with
          | .lt lhs rhs => Expr.le lhs rhs
          | _ => cond
        else cond
      .loop pre condition (perturb mutation loopBody)
        (if mutation == "post-skipped" then [] else perturb mutation post)
  | ControlFlow.Program.atom _ => statement
  | .call name results body => .call name results (perturb mutation body)
  | .leaveCall => statement

private def bytesHex (bytes : List UInt8) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun b =>
    [Compiler.Hex.hexDigit (b.toNat / 16), Compiler.Hex.hexDigit (b.toNat % 16)])

private def evaluate (root : ObservedControlRoot) (row : Json) : Except String Json := do
  let words ← (← row.getObjValAs? (Array String) "words").toList.mapM fun s =>
    match s.toNat? with
    | some value => Except.ok value
    | none => Except.error "invalid word"
  let fuel ← row.getObjValAs? Nat "fuel"
  let result ← ObservedExecution.executeRoot { control := root, fields := [] }
    Differential.oracle fuel Verity.defaultState words
  let (status, data) := match result with
    | none => ("exhausted", "0x")
    | some final =>
        (if final.invalid then "invalid" else if final.success then "ok" else "revert",
          bytesHex final.data)
  return Json.mkObj [("id", ← row.getObjVal? "id"), ("status", toJson status),
    ("data", toJson data)]

/-- Lower actual pinned-solc function ASTs, then execute their observed programs. -/
elab "observed_control_cases " input:str " output " output:str : command => do
  let bundle ← match Json.parse (← IO.FS.readFile input.getString) with
    | .ok value => pure value
    | .error error => throwError "{error}"
  let get {α} [FromJson α] (key : String) : CommandElabM α :=
    match bundle.getObjValAs? α key with
    | .ok value => pure value
    | .error error => throwError "{error}"
  let source : String ← get "source"
  let names : List String ← get "names"
  let functions : Array Json ← get "functions"
  let cases : Array Json ← get "cases"
  let mutation : String ← get "mutation"
  let mut rows : Array Json := #[]
  let mut compiled : Array Json := #[]
  let mut rejected : Array String := #[]
  for fn in functions do
    let .ok name := fn.getObjValAs? String "name" | throwError "missing function name"
    let .ok id := fn.getObjValAs? Nat "id" | throwError "missing function id"
    let env := { SolidityImport.Env.init with
      legacyWrapping := true, unchecked := true, sourceNames := names,
      currentFile := "Source.sol", files := RBMap.empty.insert "Source.sol" source.toUTF8,
      funs := RBMap.empty.insert id fn }
    let expectedRejection := match name with
      | "unguarded" | "staleGuard" => some "division/modulo needs a nonzero literal"
      | "viewOnly" => some "observed control roots currently require pure Solidity 0.7.6 functions"
      | "unnamedResult" => some "observed control returns must be named"
      | _ => none
    if let some expected := expectedRejection then
      let diagnostic ← liftTermElabM do
        try
          discard <| (lowerObservedControlRoot fn).run' env
          return ""
        catch error => return ← error.toMessageData.toString
      unless diagnostic.contains "[solidity-import:unsupported]" &&
          diagnostic.contains expected do
        throwError "{name} needs its located rejection ({expected}): {diagnostic}"
      rejected := rejected.push name
    else
      let root ← liftTermElabM <| (lowerObservedControlRoot fn).run' env
      let root := { root with body := perturb mutation root.body }
      let .ok code := ControlCodegen.scalarFrame root.params root.body |
        throwError "{name}: observed code generation failed"
      compiled := compiled.push (Json.mkObj [("name", toJson name), ("body", toJson code)])
      for row in cases do
        if (row.getObjValAs? String "function").toOption == some name then
          match evaluate root row with
          | .ok result => rows := rows.push result
          | .error error => throwError "{name}: {error}"
  IO.FS.writeFile output.getString (Json.mkObj
    [("observations", toJson rows), ("compiled", toJson compiled),
      ("rejected", toJson rejected)]).pretty
