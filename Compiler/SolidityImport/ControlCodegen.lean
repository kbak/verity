import Compiler.SolidityImport.ControlFlow
import Compiler.CompilationModel.Compile
import Compiler.CompilationModel.ParamLoading
import Compiler.Yul.PrettyPrint

/-! Experimental structured-control code generation. Native Yul loop transfers
are rendered directly; scalar leaves use the existing compiler. This component
is not a refinement theorem or an extension of the bounded-model proof surface. -/

namespace Compiler.CompilationModel.SolidityImport.ControlCodegen
open ControlFlow Compiler.Yul

private def line (indent : Nat) (text : String) : String :=
  String.ofList (List.replicate (2 * indent) ' ') ++ text

/-- Collect names in one traversal; intersecting with the enclosing scope finds captures. -/
private partial def usedNames (body : List (Program Stmt Expr))
    (acc : Std.HashSet String := {}) : Std.HashSet String := Id.run do
  let mut acc := acc
  for statement in body do
    match statement with
    | Program.atom stmt => acc := (collectStmtNames stmt).foldl (·.insert ·) acc
    | .branch pre cond yes no | .loop pre cond yes no =>
        acc := (collectStmtListNames pre ++ collectExprNames cond).foldl (·.insert ·) acc
        acc := usedNames no (usedNames yes acc)
    | .call _ _ statements => acc := usedNames statements acc
    | .breakLoop | .continueLoop | .leaveCall => pure ()
  return acc

/-- Render scalar structured control with native break/continue. Condition
preludes execute at every test, and continue reaches the for-loop postlude. -/
private partial def renderBody (body : List (Program Stmt Expr)) (scope : List String := [])
    (depth : Nat := 0) (indent : Nat := 0) (fields : List Field := [])
    (inCall : Bool := false) (events : List EventDef := []) :
    StateT (Array (List String)) (Except String) (List String) := do
  let mut chunks : Array (List String) := #[]
  let mut names := scope
  for statement in body do
    match statement with
    | Program.atom stmt =>
        chunks := chunks.push (ppStmts indent
          (← compileStmt fields events (inScopeNames := names) (stmt := stmt)))
        names := collectStmtBindNames stmt ++ names
    | .branch prelude condition yes no =>
        let pre ← compileStmtList fields events (inScopeNames := names) (stmts := prelude)
        let branchNames := prelude.flatMap collectStmtBindNames ++ names
        let test ← compileExpr fields (expr := condition)
        let yesCode ← renderBody yes branchNames depth (indent + 1) fields inCall events
        let noCode ← renderBody no branchNames depth (indent + 1) fields inCall events
        chunks := chunks.push (ppStmts indent pre ++
          [line indent s!"switch {ppExpr test}", line indent "case 0 {"] ++ noCode ++
          [line indent "}", line indent "default {"] ++ yesCode ++ [line indent "}"])
        names := branchNames
    | .loop prelude condition loopBody postlude =>
        let pre ← compileStmtList fields events (inScopeNames := names) (stmts := prelude)
        let loopNames := prelude.flatMap collectStmtBindNames ++ names
        let test ← compileExpr fields (expr := condition)
        let postCode ← renderBody postlude names depth (indent + 1) fields inCall events
        let bodyCode ← renderBody loopBody loopNames (depth + 1) (indent + 1) fields inCall events
        chunks := chunks.push ([line indent "for {} 1 {"] ++ postCode ++
          [line indent "} {"] ++ ppStmts (indent + 1) pre ++
          [line (indent + 1) ("if iszero(" ++ ppExpr test ++ ") { break }")] ++
          bodyCode ++ [line indent "}"])
    | .breakLoop =>
        unless depth > 0 do throw "break outside a loop body"
        chunks := chunks.push [line indent "break"]
    | .continueLoop =>
        unless depth > 0 do throw "continue outside a loop body"
        chunks := chunks.push [line indent "continue"]
    | .call name results callBody =>
        let used := usedNames callBody
        let captures := names.filter (fun n => used.contains n && !results.contains n)
        let code ← renderBody callBody (results ++ captures) 0 (indent + 1) fields true events
        let returns := if results.isEmpty then "" else " -> " ++ ", ".intercalate results
        let assign := if results.isEmpty then "" else ", ".intercalate results ++ " := "
        modify fun definitions => definitions.push
          (["function " ++ name ++ "(" ++ ", ".intercalate captures ++ ")" ++
              returns ++ " {"] ++ code ++ ["}"])
        chunks := chunks.push
          [line indent (assign ++ name ++ "(" ++ ", ".intercalate captures ++ ")")]
    | .leaveCall =>
        unless inCall do throw "helper return outside a helper"
        chunks := chunks.push [line indent "leave"]
  return chunks.toList.flatten

/-- Compile a scalar call frame for canonical calldata. Dispatch, arbitrary
ABI-input equivalence and transaction rollback are separate obligations. -/
def scalarFrame (params : List Param) (body : List (Program Stmt Expr))
    (fields : List Field := []) (events : List EventDef := []) :
    Except String String := do
  unless params.all (isScalarParamType ·.ty) do throw "observed frame requires scalar parameters"
  let loads := params.zipIdx.flatMap fun (param, index) =>
    genScalarLoad (fun offset => .call "calldataload" [offset]) param.name param.ty
      (4 + 32 * index)
  let preamble := ["mstore(64, 128)", "if callvalue() { revert(0, 0) }",
    s!"if lt(calldatasize(), {4 + 32 * params.length}) " ++ "{ revert(0, 0) }"]
  let (code, definitions) ← (renderBody body (params.map (·.name)) (fields := fields) (events := events)).run #[]
  return "\n".intercalate (definitions.toList.flatten ++ ["{"] ++
    preamble ++ ppStmts 0 loads ++ code ++ ["}"])

end Compiler.CompilationModel.SolidityImport.ControlCodegen
