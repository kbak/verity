import Compiler.SolidityImport.ExprHelpers

/-! Legacy flat memory records are read-only in this slice. Scalarizing their
fields preserves reads and forwarding only while every reached helper rejects
writes, reference rebinding, storage copies, and pointer-observing assembly. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyStructs
open Lean

/-- Resolve solc's declaration identity, never a textual struct name. -/
def declaration? (node : Json) (env : Env) : Option Json := do
  let td ← field? node "typeDescriptions"
  let tid ← optStr td "typeIdentifier"
  guard (tid.startsWith "t_struct$_")
  let segment ← (tid.splitOn "_$").getLast?
  let id ← (String.ofList (segment.toList.takeWhile Char.isDigit)).toNat?
  env.structs.find? id

/-- Only scalar fields have the value representation admitted here. -/
def scalar (ty : String) : Bool :=
  ty == "bool" || ty == "address" || ty == "address payable" ||
  (fixedBytesWidth? ty).isSome || (signedBitsOf ty).isSome ||
  (ty.startsWith "uint" && (bitsOf ty).any fun n => 0 < n && n ≤ 256 && n % 8 == 0)

/-- A member read is bound to its memory receiver and original field declaration. -/
def memoryMember (node : Json) (env : Env) : Bool :=
  (do
    guard (optStr node "nodeType" == some "MemberAccess")
    let base ← field? node "expression"
    let ty ← (field? base "typeDescriptions").bind (optStr · "typeString")
    guard (ty.startsWith "struct " && ty.endsWith " memory" && !ty.contains '[')
    let decl ← declaration? base env
    let members ← (field? decl "members").bind (·.getArr?.toOption)
    let id ← (field? node "referencedDeclaration").bind (·.getNat?.toOption)
    let member ← members.find? fun m => (field? m "id").bind (·.getNat?.toOption) == some id
    guard (optStr member "name" == optStr node "memberName")
    let memberTy ← (field? member "typeDescriptions").bind (optStr · "typeString")
    guard ((field? node "typeDescriptions").bind (optStr · "typeString") == some memberTy)
    return scalar memberTy : Option Bool).getD false

/-- Total scalar syntax for constructor siblings. Calls and indexed reads need
separate evaluation-order evidence when more than one argument can fail. -/
partial def totalArgument (node : Json) : Bool :=
  let kind := optStr node "nodeType" |>.getD ""
  if #["Identifier", "Literal", "ElementaryTypeNameExpression", "UserDefinedTypeName"].contains kind
    then true
  else if kind == "MemberAccess" then
    (field? node "expression").any totalArgument
  else if kind == "FunctionCall" && optStr node "kind" == some "typeConversion" then
    ((field? node "typeDescriptions").bind (optStr · "typeString")).any scalar &&
      ((field? node "arguments").bind (·.getArr?.toOption)).any (·.all totalArgument)
  else if kind == "UnaryOperation" && (optStr node "operator").any
      (#["-", "!", "~"].contains ·) then
    (field? node "subExpression").any totalArgument
  else if kind == "BinaryOperation" && (optStr node "operator").any
      (#["+", "-", "*", "==", "!=", "<", "<=", ">", ">="].contains ·) then
    #["leftExpression", "rightExpression"].all fun key => (field? node key).any totalArgument
  else if kind == "TupleExpression" then
    ((field? node "components").bind (·.getArr?.toOption)).any (·.all totalArgument)
  else false

/-- Find memory references even when assignment targets are tuple components. -/
private partial def mutationTarget (node : Json) (env : Env) : Bool :=
  memoryMember node env ||
    ((field? node "typeDescriptions").bind (optStr · "typeString")).any
      (·.startsWith "struct ") ||
    (optStr node "nodeType" == some "TupleExpression" &&
      ((field? node "components").bind (·.getArr?.toOption)).any
        (·.any (mutationTarget · env)))

/-- Validate each reached record use before common lowering can scalarize it. -/
def validate (node : Json) : M Unit := do
  let kind := optStr node "nodeType" |>.getD ""
  let ty := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
  if ty.startsWith "struct " then
    unless !ty.contains '[' &&
        (kind == "UserDefinedTypeName" || ty.endsWith " memory" ||
          (kind == "VariableDeclaration" && optStr node "storageLocation" == some "memory")) do
      failAt node ("Solidity 0.7.6 structs require scalar memory records; " ++
        "storage references are outside this slice")
    let some decl := declaration? node (← get)
      | failAt node "unresolved Solidity 0.7.6 memory struct declaration"
    for member in (← mArr (← mField decl "members")) do
      unless scalar (← mType member) do
        failAt member "Solidity 0.7.6 memory structs require scalar fields"
  if kind == "FunctionDefinition" then
    let params ← mArr (← mField (← mField node "parameters") "parameters")
    if #[some "public", some "external"].contains (optStr node "visibility") then
      for param in params do
        if (← mType param).startsWith "struct " then
          failAt param "Solidity 0.7.6 struct ABI parameters are outside the memory slice"
    for ret in (← mArr (← mField (← mField node "returnParameters") "parameters")) do
      if (← mType ret).startsWith "struct " then
        failAt ret "Solidity 0.7.6 struct returns are outside the memory slice"
  let target := if kind == "Assignment" then field? node "leftHandSide"
    else if kind == "UnaryOperation" && (optStr node "operator").any
        (#["++", "--", "delete"].contains ·) then field? node "subExpression" else none
  if let some target := target then
    if mutationTarget target (← get) then
      failAt target ("Solidity 0.7.6 memory struct writes and rebinding " ++
        "are outside the read-only slice")

private partial def findNode? (predicate : Json → Bool) (node : Json) : Option Json :=
  if predicate node then some node else
    match node with
    | .arr xs => xs.findSome? (findNode? predicate)
    | .obj fields => fields.toList.findSome? (fun (_, child) => findNode? predicate child)
    | _ => none

/-- Flattening does not preserve allocation addresses. Reject assembly throughout
reached declarations, including helpers/modifiers without a direct record argument. -/
def validateClosure : M Unit := do
  let env ← get
  let declarations := env.included.filterMap fun reached =>
    env.funs.find? reached.declId <|> env.modifiers.find? reached.declId
  let hasStruct := declarations.any fun node =>
    (findNode? (fun n =>
      ((field? n "typeDescriptions").bind (optStr · "typeString")).any
        (·.startsWith "struct ")) node).isSome
  if hasStruct then
    for declaration in declarations do
      if let some assembly := findNode?
          (fun n => optStr n "nodeType" == some "InlineAssembly") declaration then
        failAt assembly "legacy memory structs cannot share a reached closure with assembly"

end Compiler.CompilationModel.SolidityImport.LegacyStructs
