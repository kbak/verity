import Compiler.SolidityImport.LegacyControlFlow

/-! Conservative admission for the initial Solidity 0.7.6 scalar slice.
The existing lowering remains responsible for admitting individual constructs.
This additional boundary prevents newer failure, ABI, and conversion semantics
from being silently applied to a legacy declaration. -/

open Lean
namespace Compiler.CompilationModel.SolidityImport

/-- Admit the separate terminal-revert and read-only straight-line Yul forms.
The common traversal keeps every other control-flow/effect node rejected. -/
private partial def validateLegacyYul (memoryRevert : Bool) (node : Json) : M Unit := do
  match node with
  | .arr xs => xs.forM (validateLegacyYul memoryRevert)
  | .obj fields =>
      if let some kind := optStr node "nodeType" then
        let common := #["YulBlock", "YulVariableDeclaration", "YulTypedName",
          "YulLiteral", "YulIdentifier", "YulFunctionCall"]
        let extra := if memoryRevert then "YulExpressionStatement" else "YulAssignment"
        unless common.contains kind || kind == extra do
          failAt node (if memoryRevert then
            "Solidity 0.7.6 memory-revert assembly must be straight-line"
            else "Solidity 0.7.6 assembly requires a terminal memory revert or read-only decoding")
        if kind == "YulFunctionCall" then
          let name := (field? node "functionName").bind (optStr · "name")
          let builtins := if memoryRevert then
            #[some "mload", some "mstore", some "add", some "revert"]
            else #[some "mload", some "add", some "sub", some "mul", some "byte"]
          unless builtins.contains name do
            failAt node (if memoryRevert then
              "Solidity 0.7.6 memory-revert assembly builtin is unsupported"
              else "Solidity 0.7.6 read-only assembly builtin is unsupported")
      for (_, child) in fields do validateLegacyYul memoryRevert child
  | _ => pure ()

/-- Read positions exclude declarations and assignment targets. A bounded byte
assignment is allowed, but reading a narrow Solidity variable still requires
tracking solc's dirty bits, even when its high-level value was cleaned. -/
private partial def yulReadPositions (node : Json)
    (positions : Std.HashSet String := {}) : Std.HashSet String := Id.run do
  match node with
  | .arr xs => return xs.foldl (fun acc child => yulReadPositions child acc) positions
  | .obj fields =>
      if optStr node "nodeType" == some "YulIdentifier" then
        return (optStr node "src").map positions.insert |>.getD positions
      let mut positions := positions
      for (key, child) in fields do
        unless key == "variableNames" || key == "variables" do
          positions := yulReadPositions child positions
      return positions
  | _ => return positions

/-- Reject dirty narrow reads at both scalar and statement assembly entry points. -/
def validateLegacyAssemblyReads (node : Json) : M Unit := do
  let ast ← mField node "AST"
  let stmts ← mArr (← mField ast "statements")
  -- The existing terminal-revert path applies its stricter narrow-reference rule.
  if stmts.back?.any (fun stmt =>
      (((field? stmt "expression").bind (field? · "functionName")).bind
        (optStr · "name")) == some "revert") then return
  let reads := yulReadPositions ast
  let env ← get
  for ref in (← mArr (← mField node "externalReferences")) do
    if reads.contains (← mStr (← mField ref "src")) then
      let id ← mNat (← mField ref "declaration")
      if let some ty := env.scalarTy.find? id then
        unless isFullWordYulScalar ty do
          unless (env.values.find? id).any (fun | .literal _ => true | _ => false) do
            failAt node "Solidity 0.7.6 assembly reads require full-word or literal scalars"

/-- Narrow assignment results need an explicit bound in the legacy assembly
slice; enforce it for named results as well as ordinary writable locals. -/
def validateLegacyYulAssignment (node : Json) (ty : ParamType) (rhs : Expr) : M Unit := do
  unless isFullWordYulScalar ty || isProvablyBoundedYulExpr ty rhs do
    failAt node "Solidity 0.7.6 Yul assignment to narrow local requires a bounded value"

/-- Check every reached declaration, including helper bodies. Rejected constructs
need separate legacy semantics and differential evidence before admission. -/
partial def validateLegacyDeclaration (node : Json) : M Unit := do
  match node with
  | .arr children => children.forM validateLegacyDeclaration
  | .obj fields =>
    if optStr node "nodeType" == some "InlineAssembly" then
      let ast ← mField node "AST"
      let stmts ← mArr (← mField ast "statements")
      if stmts.back?.any (fun stmt =>
          (((field? stmt "expression").bind (field? · "functionName")).bind
            (optStr · "name")) == some "revert") then
        validateLegacyYul true ast
      else
        validateLegacyYul false ast
      return
    if let some kind := optStr node "nodeType" then
      unless #["FunctionDefinition", "ParameterList", "VariableDeclaration", "Block",
          "ExpressionStatement", "VariableDeclarationStatement", "IfStatement", "Return",
          "BinaryOperation", "UnaryOperation", "Assignment", "Identifier", "Literal",
          "ElementaryTypeName", "ElementaryTypeNameExpression", "FunctionCall",
          "MemberAccess", "IndexAccess", "Mapping", "TupleExpression",
          "UserDefinedTypeName", "OverrideSpecifier", "StructuredDocumentation",
          "ForStatement", "WhileStatement"].contains kind do
        failAt node s!"Solidity 0.7.6 scalar slice does not support {kind}"
      if kind == "FunctionDefinition" then
        validateLegacyControlFlow node
        unless #[some "pure", some "view"].contains (optStr node "stateMutability") do
          failAt node "Solidity 0.7.6 scalar slice requires a read-only function"
      if let some ty := (field? node "typeDescriptions").bind (optStr · "typeString") then
        if ty.contains '[' || ty.startsWith "struct " || ty.startsWith "enum " ||
            (ty.startsWith "int" && !ty.startsWith "int_const") ||
            (ty.startsWith "bytes " && ty != "bytes memory") || ty.startsWith "string " then
          failAt node s!"Solidity 0.7.6 scalar slice does not support type {ty}"
      if kind == "FunctionDefinition" then
        for ret in (← mArr (← mField (← mField node "returnParameters") "parameters")) do
          if (← mType ret) == "bytes" then
            failAt ret "Solidity 0.7.6 dynamic bytes returns are outside the decoding slice"
      if kind == "VariableDeclaration" then
        if (← mType node) == "bytes" then
          unless optStr node "storageLocation" == some "memory" do
            failAt node "Solidity 0.7.6 byte decoding requires bytes memory"
      if kind == "VariableDeclarationStatement" then
        let decls ← mArr (← mField node "declarations")
        let hasBytes ← decls.anyM fun d =>
          if d.isNull then pure false else return (← mType d) == "bytes"
        if hasBytes then
          let init := field? node "initialValue" |>.getD Json.null
          unless optStr init "nodeType" == some "Identifier" do
            failAt node "Solidity 0.7.6 bytes locals require an existing memory buffer"
          unless (← mType init) == "bytes memory" do
            failAt node "Solidity 0.7.6 bytes locals require an existing memory buffer"
      if kind == "FunctionCall" then
        if (← mType node) == "bytes memory" then
          failAt node "Solidity 0.7.6 byte construction is outside the decoding slice"
      if kind == "Assignment" then
        if (← mType (← mField node "leftHandSide")) == "bytes memory" then
          let rhs ← mField node "rightHandSide"
          unless optStr rhs "nodeType" == some "Identifier" && (← mType rhs) == "bytes memory" do
            failAt node "Solidity 0.7.6 bytes assignment requires an existing memory buffer"
      if kind == "IndexAccess" then
        let base ← mField node "baseExpression"
        if (← mType base) == "bytes memory" then
          failAt node "Solidity 0.7.6 bytes indexing may execute INVALID"
        if (fixedBytesWidth? (← mType base)).isSome then
          failAt node "Solidity 0.7.6 fixed-bytes indexing may execute INVALID"
      if kind == "FunctionCall" && optStr node "kind" == some "typeConversion" then
        let target := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
        unless target.startsWith "uint" || target.startsWith "address" ||
            (fixedBytesWidth? target).isSome || target.startsWith "contract " do
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
          -- The lowering independently resolves and validates the declaration,
          -- receiver, argument types and ABI-v1 bytes4 return transport.
          unless ty == "function (bytes32,bytes memory) view external returns (bytes4)" do
            failAt node "Solidity 0.7.6 external calls require the ABI-v1 bytes4 view slice"
        if optStr callee "nodeType" == some "Identifier" then
          -- Legacy builtins retain duplicate negative overloadedDeclarations.
          -- Ordinary reference/overload resolution is checked by the lowering.
          if let some id := (field? callee "referencedDeclaration").bind (·.getInt?.toOption) then
            let allowed := #[some "require", some "revert", some "ecrecover"]
            if id < 0 && !allowed.contains (optStr callee "name") then
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
