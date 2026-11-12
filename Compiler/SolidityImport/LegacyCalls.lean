import Compiler.SolidityImport.ExprHelpers
import Verity.Core.Model.ECM

/-! Narrow generic lowering of legacy assembly calls. Only whole assignment
values with empty output or a CALL scratch word at zero are admitted. No effectful nested operands,
Yul control flow, implicit code-existence check or automatic failure bubbling. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyCalls
open Lean

private def named (node : Json) (name : String) : Bool :=
  optStr node "nodeType" == some "YulFunctionCall" &&
    ((field? node "functionName").bind (optStr · "name")) == some name

private def args (node : Json) : Array Json :=
  ((field? node "arguments").bind (·.getArr?.toOption)).getD #[]

private def literal? (node : Json) : Option Nat := do
  guard (optStr node "nodeType" == some "YulLiteral")
  guard (optStr node "kind" == some "number")
  let value ← optStr node "value"
  Compiler.Hex.parseHexNat? value <|> value.toNat?

/-- Source positions whose full value is immediately truncated by the EVM's
160-bit call-address operand. Other narrow assembly reads keep their guards. -/
partial def maskedTargets (node : Json) : Std.HashSet String := Id.run do
  let mut found : Std.HashSet String := {}
  match node with
  | .arr xs => for child in xs do found := found.union (maskedTargets child)
  | .obj fields =>
      if named node "call" || named node "delegatecall" then
        let target := (args node).getD 1 Json.null
        if optStr target "nodeType" == some "YulIdentifier" then
          if let some src := optStr target "src" then found := found.insert src
      for (_, child) in fields do found := found.union (maskedTargets child)
  | _ => pure ()
  return found

/-- A Yul local retains a proven boolean bound only if it is never reassigned. -/
partial def assignsName (node : Json) (name : String) : Bool :=
  match node with
  | .arr children => children.any (assignsName · name)
  | .obj fields =>
      (optStr node "nodeType" == some "YulAssignment" &&
        (((field? node "variableNames").bind (·.getArr?.toOption)).getD #[]).any
          (fun target => optStr target "name" == some name)) ||
      fields.toList.any (fun (_, child) => assignsName child name)
  | _ => false

/-- A size switch immediately after a scratch-word CALL can establish that all
32 bytes were overwritten. Short and unguarded reads retain their rejection. -/
def scratchWordSwitch (statements : Array Json) (index : Nat) (selector : Json) : Bool :=
  if index == 0 || !named selector "returndatasize" || !(args selector).isEmpty then false
  else
    let previous := statements[index - 1]!
    let value := (field? previous "value").getD Json.null
    let operands := args value
    #[some "YulVariableDeclaration", some "YulAssignment"].contains
        (optStr previous "nodeType") && named value "call" && operands.size == 7 &&
      literal? operands[5]! == some 0 && literal? operands[6]! == some 32

/-- Raw call operands are effect-free; the target is cleaned by the opcode,
and the success bit is explicitly bounded for bool assignment. -/
def lower? (node : Json) (leaf : Json → M Val) : M (Option Val) := do
  unless (← get).legacyWrapping do return none
  let delegated := named node "delegatecall"
  unless delegated || named node "call" do return none
  let operands := args node
  let count := if delegated then 4 else 5
  let outputSize := literal? (operands.getD (count + 1) Json.null)
  unless operands.size == count + 2 && literal? operands[count]! == some 0 &&
      (outputSize == some 0 || (!delegated && outputSize == some 32)) do
    failAt node "legacy raw calls require empty output or one scratch word at zero"
  let mut values : List Expr := []
  let mut pre : Array Stmt := #[]
  for i in [:count] do
    let operand := operands[i]!
    let value ← leaf operand
    unless value.pre.isEmpty || (i == 0 && (← get).sourceGas &&
        value.pre.all (fun statement => match statement with
          | .ecm mod [] => match mod.byteTransport with
            | some (.sourceGasRead ..) => true
            | _ => false
          | _ => false)) do
      failAt operand "effectful legacy raw call operand"
    pre := pre ++ value.pre
    values := values ++ [value.expr]
  let result ← fresh
  pre := pre.push (.ecm (Compiler.ECM.SolidityRawCall.module result delegated) values)
  if outputSize == some 32 then
    -- CALL overwrites only min(outputSize, returndataSize), including on REVERT.
    let size ← fresh
    pre := pre ++ #[.letVar size (.literal 32),
      .ite (.lt .returndataSize (.literal 32)) [.assignVar size .returndataSize] [],
      .returndataCopy (.literal 0) (.literal 0) (.localVar size)]
  return some { pre, expr := .logicalNot (.logicalNot (.localVar result)) }

/-- Exact terminal forwarding block: a local free-pointer snapshot, a complete
return-buffer copy, and a revert of those bytes. No live memory continuation. -/
def forwardingRevert (node : Json) : Bool := Id.run do
  let statements := ((field? node "AST").bind (field? · "statements") |>.bind
    (·.getArr?.toOption)).getD #[]
  if statements.size != 3 then return false
  let first := statements[0]!
  if optStr first "nodeType" != some "YulVariableDeclaration" then return false
  let vars := ((field? first "variables").bind (·.getArr?.toOption)).getD #[]
  if vars.size != 1 then return false
  let some localName := optStr vars[0]! "name" | return false
  let init := (field? first "value").getD Json.null
  if !named init "mload" || (args init).size != 1 || literal? (args init)[0]! != some 64 then
    return false
  let isPointer := fun n => optStr n "nodeType" == some "YulIdentifier" &&
    optStr n "name" == some localName
  let isSize := fun n => named n "returndatasize" && (args n).isEmpty
  let copy := (field? statements[1]! "expression").getD Json.null
  let stop := (field? statements[2]! "expression").getD Json.null
  return optStr statements[1]! "nodeType" == some "YulExpressionStatement" &&
    optStr statements[2]! "nodeType" == some "YulExpressionStatement" &&
    named copy "returndatacopy" && (args copy).size == 3 &&
    isPointer (args copy)[0]! && literal? (args copy)[1]! == some 0 && isSize (args copy)[2]! &&
    named stop "revert" && (args stop).size == 2 &&
    isPointer (args stop)[0]! && isSize (args stop)[1]!

end Compiler.CompilationModel.SolidityImport.LegacyCalls
