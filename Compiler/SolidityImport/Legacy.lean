import Compiler.SolidityImport.ExprHelpers

/-! Conservative admission for the initial Solidity 0.7.6 scalar slice.
The existing lowering remains responsible for admitting individual constructs.
This additional boundary prevents newer failure, ABI, and conversion semantics
from being silently applied to a legacy declaration. -/

open Lean
namespace Compiler.CompilationModel.SolidityImport

/-- The admitted legacy assembly builds memory and always reverts. Other Yul
control flow, loads and side effects remain outside this extension. -/
private partial def validateLegacyRevertYul (node : Json) : M Unit := do
  match node with
  | .arr xs => xs.forM validateLegacyRevertYul
  | .obj fields =>
      if let some kind := optStr node "nodeType" then
        unless #["YulBlock", "YulVariableDeclaration", "YulTypedName", "YulLiteral",
            "YulIdentifier", "YulFunctionCall", "YulExpressionStatement"].contains kind do
          failAt node "Solidity 0.7.6 memory-revert assembly must be straight-line"
        if kind == "YulFunctionCall" then
          let name := (field? node "functionName").bind (optStr · "name")
          unless #[some "mload", some "mstore", some "add", some "revert"].contains name do
            failAt node "Solidity 0.7.6 memory-revert assembly builtin is unsupported"
      for (_, child) in fields do validateLegacyRevertYul child
  | _ => pure ()

/-- Check every reached declaration, including helper bodies. Rejected constructs
need separate legacy semantics and differential evidence before admission. -/
partial def validateLegacyDeclaration (node : Json) : M Unit := do
  match node with
  | .arr children => children.forM validateLegacyDeclaration
  | .obj fields =>
    if optStr node "nodeType" == some "InlineAssembly" then
      let ast ← mField node "AST"
      let stmts ← mArr (← mField ast "statements")
      unless stmts.back?.any (fun stmt =>
          (((field? stmt "expression").bind (field? · "functionName")).bind
            (optStr · "name")) == some "revert") do
        failAt node "Solidity 0.7.6 assembly requires a terminal memory revert"
      validateLegacyRevertYul ast
      return
    if let some kind := optStr node "nodeType" then
      unless #["FunctionDefinition", "ParameterList", "VariableDeclaration", "Block",
          "ExpressionStatement", "VariableDeclarationStatement", "IfStatement", "Return",
          "BinaryOperation", "UnaryOperation", "Assignment", "Identifier", "Literal",
          "ElementaryTypeName", "ElementaryTypeNameExpression", "FunctionCall",
          "MemberAccess", "IndexAccess", "Mapping", "TupleExpression",
          "UserDefinedTypeName", "OverrideSpecifier", "StructuredDocumentation"].contains kind do
        failAt node s!"Solidity 0.7.6 scalar slice does not support {kind}"
      if kind == "FunctionDefinition" then
        unless #[some "pure", some "view"].contains (optStr node "stateMutability") do
          failAt node "Solidity 0.7.6 scalar slice requires a read-only function"
      if let some ty := (field? node "typeDescriptions").bind (optStr · "typeString") then
        if ty.contains '[' || ty.startsWith "struct " || ty.startsWith "enum " ||
            (ty.startsWith "int" && !ty.startsWith "int_const") ||
            ty.startsWith "bytes " || ty.startsWith "string " then
          failAt node s!"Solidity 0.7.6 scalar slice does not support type {ty}"
      if kind == "IndexAccess" then
        let base ← mField node "baseExpression"
        if (fixedBytesWidth? (← mType base)).isSome then
          failAt node "Solidity 0.7.6 fixed-bytes indexing may execute INVALID"
      if kind == "BinaryOperation" || kind == "Assignment" then
        if #[some "/", some "%", some "/=", some "%="].contains (optStr node "operator") then
          failAt node ("Solidity 0.7.6 division/modulo may execute INVALID; " ++
            "legacy exceptional halt is not modeled")
      if kind == "FunctionCall" && optStr node "kind" == some "typeConversion" then
        let target := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
        unless target.startsWith "uint" || target.startsWith "address" ||
            (fixedBytesWidth? target).isSome do
          failAt node "Solidity 0.7.6 scalar slice admits only unsigned/address conversions"
        for arg in (← mArr (← mField node "arguments")) do
          let source := (field? arg "typeDescriptions").bind (optStr · "typeString") |>.getD ""
          unless source.startsWith "uint" || source.startsWith "address" ||
              source.startsWith "int_const" || (fixedBytesWidth? source).isSome ||
              source.startsWith "literal_string " do
            failAt node "Solidity 0.7.6 scalar slice admits only unsigned/address conversions"
      if kind == "FunctionCall" && optStr node "kind" == some "functionCall" then
        let callee ← mField node "expression"
        let ty := (field? callee "typeDescriptions").bind (optStr · "typeString") |>.getD ""
        if (ty.splitOn " external").length > 1 then
          failAt node "Solidity 0.7.6 external calls are outside the scalar slice"
        if optStr callee "nodeType" == some "Identifier" then
          -- Legacy builtins retain duplicate negative overloadedDeclarations.
          -- Ordinary reference/overload resolution is checked by the lowering.
          if let some id := (field? callee "referencedDeclaration").bind (·.getInt?.toOption) then
            if id < 0 && !#[some "require", some "revert"].contains (optStr callee "name") then
              failAt node ("Solidity 0.7.6 builtin call is outside the scalar slice " ++
                "(assert/INVALID is not modeled)")
    for (_, child) in fields do
      validateLegacyDeclaration child
  | _ => pure ()

/-- Solidity 0.7.6 defaults to ABI coder v1. External decoding uses the
target contract's source unit, including for inherited functions. -/
def legacyAbiV2 (ast : Json) : Bool :=
  match (field? ast "nodes").bind (·.getArr?.toOption) with
  | none => false
  | some nodes => nodes.any fun node =>
    optStr node "nodeType" == some "PragmaDirective" &&
      (let literals := (field? node "literals").bind (·.getArr?.toOption)
       literals == some #[Json.str "experimental", Json.str "ABIEncoderV2"] ||
       literals == some #[Json.str "abicoder", Json.str "v2"])

end Compiler.CompilationModel.SolidityImport
