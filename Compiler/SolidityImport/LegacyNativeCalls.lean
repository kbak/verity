import Compiler.SolidityImport.ExprHelpers
import Verity.Core.Model.ECM

/-! Empty-calldata native CALL with an explicitly discarded return buffer. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyNativeCalls
open Lean

/-- Recognize the complete tuple declaration; all other low-level calls retain
existing admission rules. The call's implicit GAS has its own source site. -/
def applies (node : Json) : Bool :=
  let declarations := ((field? node "declarations").bind (·.getArr?.toOption)).getD #[]
  let init := (field? node "initialValue").getD Json.null
  let callee := (field? init "expression").getD Json.null
  declarations.size == 2 && !declarations[0]!.isNull && declarations[1]!.isNull &&
    optStr callee "nodeType" == some "FunctionCallOptions"

/-- Preserve low-level success/failure, value transfer and full return-buffer
replacement using the existing raw CALL transport. Implicit gas is observed
only in original-bytecode mode; functional mode uses an uncapped operand. -/
def lower (node : Json) (leaf : Json → M Val) : M (Array Stmt) := do
  unless (← get).legacyWrapping do failAt node "native value calls require Solidity 0.7.6"
  let init ← mField node "initialValue"
  let callee ← mField init "expression"
  let member ← mField callee "expression"
  let base ← mField member "expression"
  unless optStr member "nodeType" == some "MemberAccess" &&
      optStr member "memberName" == some "call" &&
      (field? member "referencedDeclaration").isNone &&
      ["address", "address payable"].contains (← mType base) do
    failAt member "native value call requires an address receiver"
  let names ← mArr (← mField callee "names")
  let options ← mArr (← mField callee "options")
  unless names == #[Json.str "value"] && options.size == 1 do
    failAt callee "native value call requires only a value option"
  let arguments ← mArr (← mField init "arguments")
  unless arguments.size == 1 && optStr arguments[0]! "nodeType" == some "Literal" &&
      optStr arguments[0]! "hexValue" == some "" do
    failAt init "native value call requires empty literal calldata"
  let target ← leaf base
  let amount ← leaf options[0]!
  unless target.pre.isEmpty && amount.pre.isEmpty do
    failAt init "native value call operands must be effect-free scalar expressions"
  let declarations ← mArr (← mField node "declarations")
  let declaration := declarations[0]!
  unless (← mType declaration) == "bool" do failAt declaration "native call result must be bool"
  let id ← mNat (← mField declaration "id")
  let name ← mStr (← mField declaration "name")
  let binding ← freshFor name
  let result := Expr.localVar binding
  modify fun e => { e with
    values := e.values.insert id result, scalarTy := e.scalarTy.insert id .bool,
    writableLocals := e.writableLocals.insert id binding,
    yulNames := e.yulNames.insert name result }
  let mut pre := #[]
  let mut gas := Expr.literal (2^256-1)
  if (← get).sourceGas then
    let observed ← fresh
    let site ← mStr (← mField init "src")
    pre := pre.push (.ecm (Compiler.ECM.SourceGasRead.module observed site) [])
    gas := .localVar observed
  let pointer ← fresh
  let size ← fresh
  let header := Expr.localVar pointer
  let length := Expr.localVar size
  let capacity := Expr.bitAnd (.add length (.literal 31)) (.bitNot (.literal 31))
  modify fun e => { e with encodingMemory := true }
  return pre ++ #[.ecm (Compiler.ECM.SolidityRawCall.module binding false)
    [gas, target.expr, amount.expr, .literal 0, .literal 0],
    .letVar size .returndataSize,
    .ite (.gt length (.literal 0)) [
      .letVar pointer (.mload (.literal 64)),
      .mstore (.literal 64) (.add (.add header (.literal 32)) capacity),
      .mstore header length,
      .returndataCopy (.add header (.literal 32)) (.literal 0) length] []]

end Compiler.CompilationModel.SolidityImport.LegacyNativeCalls
