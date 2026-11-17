import Compiler.SolidityImport.ObservedImport
import Compiler.SolidityImport.ControlDenote
import Compiler.SolidityImport.ControlCodegen
import Compiler.SolidityImport.Differential
import Compiler.SolidityImport.ObservedExecution

/-! Focused same-frame storage/helper observations using actual pinned compiler ASTs. -/
open Lean Elab Command Compiler.CompilationModel
open Compiler.CompilationModel.SolidityImport

private partial def perturb (mutation : String) (body : ControlLowering.Body)
    (inHelper : Bool := false) :
    ControlLowering.Body := body.flatMap fun statement =>
  match statement with
  | .leaveCall =>
      if mutation == "helper-return-dropped" then []
      else if mutation == "helper-return-exits-frame" then [.atom (.return (.literal 0))]
      else [statement]
  | .atom (.setStorage field _) =>
      if mutation == "storage-write-zero" && !inHelper then
        [.atom (.setStorage field (.literal 0))]
      else [statement]
  | .branch pre cond yes no =>
      [.branch pre cond (perturb mutation yes inHelper) (perturb mutation no inHelper)]
  | .loop pre cond body post =>
      [.loop pre cond (perturb mutation body inHelper) (perturb mutation post inHelper)]
  | .call name results body => [.call name results (perturb mutation body true)]
  | _ => [statement]

private def hexBytes (bytes : List UInt8) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun b =>
    [Compiler.Hex.hexDigit (b.toNat / 16), Compiler.Hex.hexDigit (b.toNat % 16)])

private def words (row : Json) (key : String) : Except String (List Nat) := do
  (← row.getObjValAs? (List String) key).mapM fun word =>
    match word.toNat? with
    | some value => .ok value
    | none => .error "invalid test word"

private def evaluate (root : ObservedImport.Root) (row : Json) : Except String Json := do
  let args ← words row "words"
  let slots ← words row "slots"
  let values ← words row "initial"
  unless slots.length == values.length do throw "initial storage length mismatch"
  let world := (slots.zip values).foldl
    (fun state (slot, value) => state.writePhysicalSlot slot (Verity.Core.Uint256.ofNat value))
    Verity.defaultState
  let some final ← ObservedExecution.executeRoot root Differential.oracle 4000 world args
    | throw "storage case exhausted without a completed observation"
  let status := if final.invalid then "invalid" else if final.success then "ok" else "revert"
  return Json.mkObj [("id", ← row.getObjVal? "id"), ("status", toJson status),
    ("data", toJson (hexBytes final.data)),
    ("storage", toJson (slots.map fun slot =>
      toString (final.world.storageWords (.slot slot)).val))]

elab "observed_storage_cases " input:str " output " output:str : command => do
  let .ok bundle := Json.parse (← IO.FS.readFile input.getString) | throwError "invalid input"
  let get {α} [FromJson α] (key : String) : CommandElabM α :=
    match bundle.getObjValAs? α key with
    | .ok value => pure value
    | .error error => throwError "{error}"
  let source : String ← get "source"
  let ast : Json ← get "ast"
  let layout : Json ← get "layout"
  let functions : Array Json ← get "functions"
  let cases : Array Json ← get "cases"
  let bases : Array Nat ← get "bases"
  let mutation : String ← get "mutation"
  let base := { SolidityImport.Env.init with
    legacyWrapping := true, unchecked := true, currentFile := "Source.sol",
    files := RBMap.empty.insert "Source.sol" source.toUTF8, linearizedBases := bases }
  let (_, indexed) ← liftTermElabM <| (ObservedSupport.indexSource "Source.sol" ast).run base
  let .ok types := layout.getObjVal? "types" | throwError "missing layout types"
  let .ok items := layout.getObjValAs? (Array Json) "storage" | throwError "missing layout"
  let mut env := { indexed with layoutTypes := types }
  for item in items do
    let .ok label := item.getObjValAs? String "label" | throwError "missing layout label"
    env := { env with layoutItems := env.layoutItems.insert label item }
  let mut observed : Array Json := #[]
  let mut compiled : Array Json := #[]
  let mut rejected : Array String := #[]
  for fn in functions do
    let .ok name := fn.getObjValAs? String "name" | throwError "missing function name"
    let expected := if name == "recursive" then some "recursive observed helper call"
      else if name == "ambiguousRecord" then
        some ("assignment expression in multi-argument call requires " ++
          "explicit evaluation-order support")
      else none
    if let some expected := expected then
      let error ← liftTermElabM do
        try
          discard <| (ObservedImport.lowerRoot fn).run' env
          return ""
        catch e => return ← e.toMessageData.toString
      unless error.contains "[solidity-import:unsupported]" &&
          error.contains expected do
        throwError "missing {name} boundary: {error}"
      rejected := rejected.push name
    else
      let root ← liftTermElabM <| (ObservedImport.lowerRoot fn).run' env
      let root := { root with control := { root.control with
        body := perturb mutation root.control.body } }
      let .ok code := ControlCodegen.scalarFrame root.control.params root.control.body root.fields
        | throwError "{name}: code generation failed"
      compiled := compiled.push (Json.mkObj [("name", toJson name), ("body", toJson code)])
      for row in cases do
        if (row.getObjValAs? String "function").toOption == some name then
          match evaluate root row with
          | .ok result => observed := observed.push result
          | .error message => throwError "{name}: {message}"
  IO.FS.writeFile output.getString (Json.mkObj [("observations", toJson observed),
    ("compiled", toJson compiled), ("rejected", toJson rejected)]).pretty
