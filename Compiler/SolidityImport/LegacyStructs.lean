import Compiler.SolidityImport.TupleReturns

/-! Legacy flat memory records remain read-only. Flat storage records retain
their storage paths through local aliases and internal helper arguments/results.
Mapping and fixed-array elements retain their storage identity; copies and rebinding remain excluded. -/
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

/-- Only one-dimensional fixed storage arrays retain a flat record element identity. -/
def fixedArray? (node : Json) : Option (Nat × Nat) := do
  let typeId ← (field? node "typeDescriptions").bind (optStr · "typeIdentifier")
  fixedStorageStructArrayType? typeId

/-- Array helper signatures are admitted through their actual internal declaration.
Each parameter and the reached body still pass the ordinary typed validation. -/
def fixedArrayFunction (node : Json) (env : Env) : Bool :=
  (do
    let id ← (field? node "referencedDeclaration").bind (·.getNat?.toOption)
    let fn ← env.funs.find? id
    guard (#[some "internal", some "private"].contains (optStr fn "visibility"))
    let params ← (field? fn "parameters").bind (field? · "parameters")
    let params ← params.getArr?.toOption
    guard (params.any fun p => (fixedArray? p).isSome)
    let returns ← (field? fn "returnParameters").bind (field? · "parameters")
    let returns ← returns.getArr?.toOption
    guard ((params ++ returns).all fun p =>
      let ty := ((field? p "typeDescriptions").bind (optStr · "typeString")).getD ""
      !ty.contains '[' || ((fixedArray? p).isSome &&
        optStr p "storageLocation" == some "storage"))
    pure true : Option Bool).getD false

/-- Only scalar fields have the value representation admitted here. -/
def scalar (ty : String) : Bool :=
  ty == "bool" || ty == "address" || ty == "address payable" ||
  (fixedBytesWidth? ty).isSome || (signedBitsOf ty).isSome ||
  (ty.startsWith "uint" && (bitsOf ty).any fun n => 0 < n && n ≤ 256 && n % 8 == 0)

/-- Literal mixed tuples use the typed tuple lowering, not scalar conditional lowering. -/
def storageTuple (node : Json) : Bool :=
  optStr node "nodeType" == some "TupleExpression" &&
    ((field? node "components").bind (·.getArr?.toOption)).any fun components =>
      components.size > 1 && components.any TupleReturns.isStorage && components.all fun c =>
        TupleReturns.isStorage c ||
          ((field? c "typeDescriptions").bind (optStr · "typeString")).any scalar

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

/-- A storage member keeps its declaration identity and scalar field type.
The common lowering independently resolves its receiver to an actual storage path. -/
def storageMember (node : Json) (env : Env) : Bool :=
  (do
    guard (optStr node "nodeType" == some "MemberAccess")
    let base ← field? node "expression"
    let ty ← (field? base "typeDescriptions").bind (optStr · "typeString")
    guard (ty.endsWith " storage ref" || ty.endsWith " storage pointer")
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
partial def totalArgument (node : Json) (wordArithmetic : Bool := false) : Bool :=
  let kind := optStr node "nodeType" |>.getD ""
  let total := fun child => totalArgument child wordArithmetic
  let ty := (field? node "typeDescriptions").bind (optStr · "typeString")
  if wordArithmetic && ty.any (·.startsWith "enum ") then false
  else if #["Identifier", "Literal", "ElementaryTypeNameExpression", "UserDefinedTypeName"].contains kind
    then true
  else if kind == "MemberAccess" then
    (field? node "expression").any total
  else if kind == "FunctionCall" && optStr node "kind" == some "typeConversion" then
    ty.any scalar &&
      ((field? node "arguments").bind (·.getArr?.toOption)).any (·.all total)
  else if wordArithmetic && kind == "FunctionCall" &&
      ((field? node "expression").bind (field? · "referencedDeclaration") >>= (·.getInt?.toOption))
        == some (-27) then true
  else if kind == "UnaryOperation" && (optStr node "operator").any
      (#["-", "!", "~"].contains ·) then
    (field? node "subExpression").any total
  else if kind == "BinaryOperation" && (optStr node "operator").any
      (fun op => #["+", "-", "*", "==", "!=", "<", "<=", ">", ">="].contains op ||
        (wordArithmetic && #["<<", ">>", "&", "|", "^"].contains op)) then
    #["leftExpression", "rightExpression"].all fun key => (field? node key).any total
  else if kind == "TupleExpression" then
    ((field? node "components").bind (·.getArr?.toOption)).any (·.all total)
  else false

/-- Find memory references even when assignment targets are tuple components. -/
private partial def mutationTarget (node : Json) (env : Env)
    (storageReturns : Array Nat) : Bool :=
  if (TupleReturns.targetId? node storageReturns).isSome then false else
  memoryMember node env ||
    ((field? node "typeDescriptions").bind (optStr · "typeString")).any
      (·.startsWith "struct ") ||
    (optStr node "nodeType" == some "TupleExpression" &&
      ((field? node "components").bind (·.getArr?.toOption)).any
        (·.any (mutationTarget · env storageReturns)))

/-- Validate each reached record use before common lowering can scalarize it. -/
def validate (node : Json) (storageReturns : Array Nat := #[]) : M Unit := do
  let kind := optStr node "nodeType" |>.getD ""
  let ty := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
  if ty.startsWith "struct " then
    let resultAssignment := kind == "Assignment" && optStr node "operator" == some "=" &&
      ((field? node "leftHandSide").bind (TupleReturns.targetId? · storageReturns)).isSome
    let mappingElement := kind == "IndexAccess" &&
      (field? node "baseExpression").bind (optStr · "nodeType") == some "Identifier" &&
      (((field? node "baseExpression").bind (field? · "typeDescriptions")).bind
        (optStr · "typeString")).any (·.startsWith "mapping(")
    let storage := (#["Identifier", "FunctionCall", "VariableDeclaration"].contains kind ||
      mappingElement ||
      (kind == "IndexAccess" && ((field? node "baseExpression").bind fixedArray?).isSome) ||
      resultAssignment) &&
      (ty.endsWith " storage ref" || ty.endsWith " storage pointer" ||
        optStr node "storageLocation" == some "storage")
    let array := fixedArray? node
    unless (!ty.contains '[' || (array.isSome &&
        (storage || kind == "ArrayTypeName" || kind == "VariableDeclaration"))) &&
        (storage || kind == "UserDefinedTypeName" || (array.isSome &&
          (kind == "ArrayTypeName" || kind == "VariableDeclaration")) || ty.endsWith " memory" ||
          (kind == "VariableDeclaration" && optStr node "storageLocation" == some "memory")) do
      failAt node (s!"Solidity 0.7.6 scalar slice does not support type {ty}; " ++
        "storage references are outside this slice")
    let env ← get
    let some decl := (array.bind fun (sid, _) => env.structs.find? sid) <|>
        declaration? node env
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
        unless optStr ret "storageLocation" == some "storage" &&
            #[some "internal", some "private"].contains (optStr node "visibility") do
          failAt ret "Solidity 0.7.6 struct returns are outside the memory slice"
  if kind == "VariableDeclarationStatement" then
    let init := field? node "initialValue" |>.getD Json.null
    let initTy := (field? init "typeDescriptions").bind (optStr · "typeString") |>.getD ""
    if initTy.startsWith "struct " &&
        (initTy.endsWith " storage ref" || initTy.endsWith " storage pointer") then
      for decl in (← mArr (← mField node "declarations")) do
        if optStr decl "storageLocation" == some "memory" then
          failAt decl "Solidity 0.7.6 storage copies to memory are outside this slice"
  let target := if kind == "Assignment" then field? node "leftHandSide"
    else if kind == "UnaryOperation" && (optStr node "operator").any
        (#["++", "--", "delete"].contains ·) then field? node "subExpression" else none
  if let some target := target then
    if mutationTarget target (← get) storageReturns then
      failAt target ("Solidity 0.7.6 memory struct writes and rebinding " ++
        "are outside the read-only slice")

private partial def findNode? (predicate : Json → Bool) (node : Json) : Option Json :=
  if predicate node then some node else
    match node with
    | .arr xs => xs.findSome? (findNode? predicate)
    | .obj fields => fields.toList.findSome? (fun (_, child) => findNode? predicate child)
    | _ => none

/-- Check allocation-address observability across all source bodies in a slice. -/
def validateBodies (declarations : Array Json) : M Unit := do
  let hasStruct := declarations.any fun node =>
    (findNode? (fun n =>
      let ty := ((field? n "typeDescriptions").bind (optStr · "typeString")).getD ""
      ty.startsWith "struct " && (ty.endsWith " memory" ||
        (optStr n "nodeType" == some "VariableDeclaration" &&
          optStr n "storageLocation" == some "memory"))) node).isSome
  if hasStruct then
    for declaration in declarations do
      if let some assembly := findNode?
          (fun n => optStr n "nodeType" == some "InlineAssembly") declaration then
        failAt assembly "legacy memory structs cannot share a reached closure with assembly"

/-- Flattening does not preserve allocation addresses. Check each reached declaration,
including helpers and modifiers without a direct record argument. -/
def validateClosure : M Unit := do
  let env ← get
  validateBodies <| env.included.filterMap fun reached =>
    env.funs.find? reached.declId <|> env.modifiers.find? reached.declId

end Compiler.CompilationModel.SolidityImport.LegacyStructs
