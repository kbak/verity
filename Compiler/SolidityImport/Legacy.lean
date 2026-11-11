import Compiler.SolidityImport.LegacyControlFlow
import Compiler.SolidityImport.LegacyAbi
import Compiler.SolidityImport.LegacyArrays
import Compiler.SolidityImport.LegacyMemory
import Compiler.SolidityImport.LegacyCalls
import Compiler.SolidityImport.LegacyVoidCalls
import Compiler.SolidityImport.LegacyBoolCalls
import Compiler.SolidityImport.LegacyStorage
import Compiler.SolidityImport.StorageLayout

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
            else #[some "mload", some "add", some "sub", some "mul", some "byte", some "chainid",
              some "call", some "delegatecall", some "returndatasize", some "sload"]
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
  let masked := LegacyCalls.maskedTargets ast
  let env ← get
  for ref in (← mArr (← mField node "externalReferences")) do
    if reads.contains (← mStr (← mField ref "src")) then
      let id ← mNat (← mField ref "declaration")
      if env.scalarArrays.contains id then
        failAt node "Solidity 0.7.6 assembly array references are outside the guarded-read slice"
      if let some ty := env.scalarTy.find? id then
        unless isFullWordYulScalar ty do
          unless (ty == .address && masked.contains (← mStr (← mField ref "src"))) ||
              env.legacyCleanParams.contains id ||
              (env.values.find? id).any (fun | .literal _ => true | _ => false) do
            failAt node "Solidity 0.7.6 assembly reads require full-word or literal scalars"

/-- A constant-slot address load is cleaned at the Solidity boundary. Later
assembly reads of narrow locals still require the existing dirty-bit checks. -/
def cleanLegacyStorageAddress (ty : ParamType) (value : Val) : Val :=
  match ty, value.expr with
  | .address, .storageArrayElement field (.literal _) =>
      if field == rawStorageFieldName then
        { value with expr := LegacyMemory.cleanScalar .address value.expr }
      else value
  | _, _ => value

/-- Narrow assignment results need an explicit bound in the legacy assembly
slice; enforce it for named results as well as ordinary writable locals. -/
def validateLegacyYulAssignment (node : Json) (ty : ParamType) (rhs : Expr) : M Unit := do
  unless isFullWordYulScalar ty || isProvablyBoundedYulExpr ty rhs do
    failAt node "Solidity 0.7.6 Yul assignment to narrow local requires a bounded value"

/-- Check every reached declaration, including helper bodies. Rejected constructs
need separate legacy semantics and differential evidence before admission.
`encodingInput` admits construction only as the direct input to the hash builtin. -/
partial def validateLegacyDeclaration (node : Json) (encodingInput : Bool := false) : M Unit := do
  match node with
  | .arr children => children.forM (validateLegacyDeclaration · encodingInput)
  | .obj fields =>
    if LegacyBoolCalls.interfaceId node (← get) then return
    if optStr node "nodeType" == some "InlineAssembly" then
      if LegacyCalls.forwardingRevert node then return
      let ast ← mField node "AST"
      let stmts ← mArr (← mField ast "statements")
      if LegacyStorage.writes ast then return
      if stmts.back?.any (fun stmt =>
          (((field? stmt "expression").bind (field? · "functionName")).bind
            (optStr · "name")) == some "revert") then
        validateLegacyYul true ast
      else if LegacyMemory.applies ast then
        LegacyMemory.validate ast
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
          "ForStatement", "WhileStatement", "ModifierDefinition", "ModifierInvocation",
          "PlaceholderStatement", "EmitStatement", "ArrayTypeName", "NewExpression"].contains kind do
        failAt node s!"Solidity 0.7.6 scalar slice does not support {kind}"
      if kind == "FunctionDefinition" || kind == "ModifierDefinition" then
        validateLegacyControlFlow node
        LegacyArrays.validateDeclaration node
      if kind == "FunctionDefinition" then
        unless #[some "pure", some "view", some "nonpayable", some "payable"].contains
            (optStr node "stateMutability") do
          failAt node "unsupported Solidity 0.7.6 function mutability"
      if let some ty := (field? node "typeDescriptions").bind (optStr · "typeString") then
        if ty.startsWith "enum " then
          let ref := (field? node "referencedDeclaration").bind (·.getNat?.toOption)
          let stored := ref.any (← get).stateVars.contains ||
            (field? node "stateVariable").any (fun x => x.getBool?.toOption == some true)
          if stored then failAt node "Solidity 0.7.6 enum storage is outside the scalar enum slice"
        let supportedArray := ty == "address[]" || ty == "address[] memory" ||
          (ty.startsWith "function (" && !(ty.replace "address[] memory" "address").contains '[')
        if (ty.contains '[' && !supportedArray) ||
            ty.startsWith "struct " ||
            (ty.startsWith "int" && !ty.startsWith "int_const") ||
            (ty.startsWith "bytes " && ty != "bytes memory" && ty != "bytes calldata") ||
            ty.startsWith "string " then
          failAt node s!"Solidity 0.7.6 scalar slice does not support type {ty}"
      if kind == "FunctionDefinition" then
        let returns ← mArr (← mField (← mField node "returnParameters") "parameters")
        let hasEnum ← returns.anyM fun p => return (← mType p).startsWith "enum "
        if hasEnum && !#[some "public", some "external"].contains (optStr node "visibility") then
          failAt node "Solidity 0.7.6 enum helper returns are outside the scalar enum slice"
        for ret in returns do
          if (← mType ret).startsWith "enum " &&
              (returns.size != 1 || optStr ret "name" != some "") then
            failAt ret "Solidity 0.7.6 enum returns require one unnamed scalar result"
        for ret in returns do
          if (← mType ret) == "bytes" then
            failAt ret "Solidity 0.7.6 dynamic bytes returns are outside the decoding slice"
      if kind == "VariableDeclaration" then
        if (← mType node) == "address[]" then
          unless optStr node "storageLocation" == some "memory" do
            failAt node "Solidity 0.7.6 address arrays require memory location"
        if (← mType node) == "bytes" then
          unless #[some "memory", some "calldata"].contains (optStr node "storageLocation") do
            failAt node "Solidity 0.7.6 byte decoding requires memory or calldata"
      if kind == "VariableDeclarationStatement" then
        let decls ← mArr (← mField node "declarations")
        if ← decls.anyM fun d =>
            if d.isNull then pure false else return (← mType d).startsWith "enum " then
          failAt node "Solidity 0.7.6 enum locals are outside the scalar enum slice"
        let hasBytes ← decls.anyM fun d =>
          if d.isNull then pure false else return (← mType d) == "bytes"
        if hasBytes then
          let init := field? node "initialValue" |>.getD Json.null
          unless init.isNull do
            unless optStr init "nodeType" == some "Identifier" &&
                (← mType init) == "bytes memory" do
              failAt node "Solidity 0.7.6 bytes locals require an existing memory buffer"
      if kind == "BinaryOperation" then
        for key in #["leftExpression", "rightExpression"] do
          if (← mType (← mField node key)).startsWith "enum " then
            unless (optStr node "operator").any
                (#["==", "!=", "<", "<=", ">", ">="].contains ·) do
              failAt node "Solidity 0.7.6 enum operands require a comparison"
      if kind == "Conditional" then
        if (← mType node).startsWith "enum " then
          failAt node "Solidity 0.7.6 enum conditionals are outside the scalar enum slice"
      if kind == "UnaryOperation" then
        if (← mType (← mField node "subExpression")).startsWith "enum " then
          failAt node "Solidity 0.7.6 enum mutations are outside the scalar enum slice"
      if kind == "FunctionCall" then
        let callee := (field? node "expression").getD Json.null
        let resolved := (field? callee "referencedDeclaration").bind (·.getNat?.toOption)
        let calleeType := (optStr ((field? callee "typeDescriptions").getD Json.null)
          "typeString").getD ""
        let voidCall := LegacyVoidCalls.applies node (← get)
        let internalCall := optStr node "kind" == some "functionCall" &&
          resolved.any (← get).funs.contains && (calleeType.splitOn " external").length == 1
        if internalCall && (← mType node).startsWith "enum " then
          failAt node "Solidity 0.7.6 enum helper returns are outside the scalar enum slice"
        for arg in (← mArr (← mField node "arguments")) do
          if (← mType arg).startsWith "enum " && !internalCall && !voidCall &&
              !(optStr node "kind" == some "typeConversion" &&
                (← mType node).startsWith "uint") then
            failAt arg "Solidity 0.7.6 enum arguments require an internal helper or conversion"
          if (← mType arg) == "bytes calldata" && !voidCall then
            unless internalCall do
              failAt arg "Solidity 0.7.6 calldata call arguments are outside the copying slice"
            unless optStr arg "nodeType" == some "Identifier" do
              failAt arg "legacy bytes helpers require an existing calldata identifier"
            if (← get).legacyAbiV2Files.contains (← get).currentFile then
              failAt arg "legacy bytes helpers require ABI coder v1 at the call site"
        if (← mType node) == "bytes memory" && !(encodingInput &&
            (LegacyPacked.isEncoding node || LegacyAbi.isEncoding node)) then
          failAt node "Solidity 0.7.6 byte construction is outside the decoding slice"
      if kind == "Assignment" then
        if (← mType (← mField node "leftHandSide")).startsWith "enum " then
          failAt node "Solidity 0.7.6 enum assignment is outside the scalar enum slice"
        if (← mType (← mField node "leftHandSide")) == "bytes calldata" then
          failAt node "Solidity 0.7.6 calldata assignment is outside the copying slice"
        if (← mType (← mField node "leftHandSide")) == "bytes memory" then
          let rhs ← mField node "rightHandSide"
          unless optStr rhs "nodeType" == some "Identifier" && (← mType rhs) == "bytes memory" do
            failAt node "Solidity 0.7.6 bytes assignment requires an existing memory buffer"
      if kind == "IndexAccess" then
        let index := field? node "indexExpression" |>.getD Json.null
        unless index.isNull do
          if (← mType index).startsWith "enum " then
            failAt node "Solidity 0.7.6 enum keys require an unsigned conversion"
        let base ← mField node "baseExpression"
        if (← mType base) == "bytes calldata" then
          failAt node "Solidity 0.7.6 calldata indexing is outside the copying slice"
        if (← mType base) == "bytes memory" then
          failAt node "Solidity 0.7.6 bytes indexing may execute INVALID"
        if (fixedBytesWidth? (← mType base)).isSome then
          failAt node "Solidity 0.7.6 fixed-bytes indexing may execute INVALID"
      if kind == "FunctionCall" && optStr node "kind" == some "typeConversion" then
        let target := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
        unless target.startsWith "uint" || target.startsWith "address" ||
            (fixedBytesWidth? target).isSome || target.startsWith "contract " ||
            target.startsWith "enum " do
          failAt node "Solidity 0.7.6 scalar slice admits only unsigned/address conversions"
        for arg in (← mArr (← mField node "arguments")) do
          let source := (field? arg "typeDescriptions").bind (optStr · "typeString") |>.getD ""
          unless source.startsWith "uint" || source.startsWith "address" ||
              source.startsWith "int_const" || source.startsWith "enum " ||
              (fixedBytesWidth? source).isSome ||
              source.startsWith "literal_string " ||
              (target.startsWith "address" && source.startsWith "contract ") do
            failAt node "Solidity 0.7.6 scalar slice admits only unsigned/address conversions"
      if kind == "FunctionCall" && optStr node "kind" == some "functionCall" then
        let callee ← mField node "expression"
        let ty := (field? callee "typeDescriptions").bind (optStr · "typeString") |>.getD ""
        if (ty.splitOn " external").length > 1 then
          -- The lowering independently resolves and validates the declaration,
          -- receiver, argument types and ABI-v1 bytes4 return transport.
          unless ty == "function (bytes32,bytes memory) view external returns (bytes4)" ||
              LegacyVoidCalls.applies node (← get) || LegacyBoolCalls.applies node (← get) do
            failAt node "Solidity 0.7.6 external calls require the ABI-v1 bytes4 view slice"
        if optStr callee "nodeType" == some "Identifier" then
          -- Legacy builtins retain duplicate negative overloadedDeclarations.
          -- Ordinary reference/overload resolution is checked by the lowering.
          if let some id := (field? callee "referencedDeclaration").bind (·.getInt?.toOption) then
            let allowed := #[some "require", some "revert", some "ecrecover", some "keccak256"]
            if id < 0 && !allowed.contains (optStr callee "name") then
              failAt node ("Solidity 0.7.6 builtin call is outside the scalar slice " ++
                "(assert/INVALID is not modeled)")
    let callee := field? node "expression" |>.getD Json.null
    let isHash := optStr node "nodeType" == some "FunctionCall" &&
      optStr callee "nodeType" == some "Identifier" &&
      optStr callee "name" == some "keccak256" &&
      ((field? callee "referencedDeclaration").bind (·.getInt?.toOption)) == some (-8)
    for (key, child) in fields do
      validateLegacyDeclaration child (isHash && key == "arguments")
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
