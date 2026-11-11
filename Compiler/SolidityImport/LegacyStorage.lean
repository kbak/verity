import Compiler.SolidityImport.ExprHelpers

/-! Narrow admission for straight-line constant-slot legacy assembly stores.
The lowering checks constant slots; existing assembly-read checks guard dirty bits. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyStorage
open Lean

/-- Only complete blocks of `sstore` with literal/identifier operands qualify.
Calls, arithmetic, memory effects, assignments and control flow remain excluded. -/
def writes (ast : Json) : Bool := Id.run do
  unless optStr ast "nodeType" == some "YulBlock" do return false
  let stmts := ((field? ast "statements").bind (·.getArr?.toOption)).getD #[]
  return !stmts.isEmpty && stmts.all fun stmt =>
    let expr := field? stmt "expression" |>.getD Json.null
    let args := ((field? expr "arguments").bind (·.getArr?.toOption)).getD #[]
    optStr stmt "nodeType" == some "YulExpressionStatement" &&
    optStr expr "nodeType" == some "YulFunctionCall" &&
    ((field? expr "functionName").bind (optStr · "name")) == some "sstore" &&
    args.size == 2 && args.all fun arg =>
      #[some "YulLiteral", some "YulIdentifier"].contains (optStr arg "nodeType")

end Compiler.CompilationModel.SolidityImport.LegacyStorage
