import Compiler.SolidityImport.LegacyStructs

/-! Bounded admission of legacy signed scalar arithmetic. Storage and
assembly need separate legacy semantics; admitting a scalar type does not admit
those uses. All arithmetic here reuses the wrapping expression lowering. -/
namespace Compiler.CompilationModel.SolidityImport.LegacySigned
open Lean

/-- Solidity hashes an integer key as a full word, extended at its declared width. -/
def mappingKeyWidth? (key value : String) : Option Nat := do
  guard (value.startsWith "uint" && (bitsOf value).isSome)
  signedBitsOf key

/-- Canonicalize the key before computing the Solidity storage address. -/
def mappingKeyWord (width : Option Nat) (key : Expr) : Expr :=
  match width with
  | some bits => if bits < 256 then .signextend (.literal (bits / 8 - 1)) key else key
  | none => key

/-- Inspect mapping key/value types without expanding unrelated struct layouts. -/
private partial def hasSignedType (node : Json) : Bool :=
  ((field? node "typeDescriptions").bind (optStr · "typeString")).any
    (fun ty => (signedBitsOf ty).isSome) ||
  (optStr node "nodeType" == some "Mapping" &&
    #["keyType", "valueType"].any (fun key => (field? node key).any hasSignedType))

/-- Storage width for a one-key unsigned-integer mapping with a narrow signed value. -/
def mappingValueWidth? (key value : String) : Option Nat := do
  guard (key.startsWith "uint" && (bitsOf key).isSome)
  let width ← signedBitsOf value
  guard (width < 256)
  return width

private def declaredMappingWidth? (decl : Json) (widthOf : String → String → Option Nat) :
    Option Nat := do
  let ty ← field? decl "typeName"
  guard (optStr ty "nodeType" == some "Mapping")
  let typeOf := fun (node : Json) => (field? node "typeDescriptions").bind (optStr · "typeString")
  widthOf (← typeOf (← field? ty "keyType")) (← typeOf (← field? ty "valueType"))

private def directMappingAccess (node : Json) (width : Nat) (env : Env) : Bool := (do
  let base ← field? node "baseExpression"
  guard (optStr base "nodeType" == some "Identifier")
  let id ← (← field? base "referencedDeclaration").getNat?.toOption
  return declaredMappingWidth? (← env.stateVars.find? id) mappingValueWidth? == some width
  : Option Bool).getD false

/-- Validate signed expressions and declaration-bound storage uses in the legacy profile. -/
def validate (node : Json) (observedLocals : Bool := false) : M Unit := do
  let kind := optStr node "nodeType" |>.getD ""
  let ty := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
  let ref := (field? node "referencedDeclaration").bind (·.getNat?.toOption)
  let env ← get
  let declaration :=
    if (field? node "stateVariable").any (fun x => x.getBool?.toOption == some true) then
      some node else ref.bind env.stateVars.find?
  if let some width := signedBitsOf ty then
    let constant := ref.any env.numericConstants.contains || declaration.any (fun d =>
      (field? d "constant").bind (·.getBool?.toOption) == some true)
    if !constant && (declaration.isSome ||
        (kind == "IndexAccess" && !directMappingAccess node width env) ||
        (kind == "MemberAccess" && !LegacyStructs.memoryMember node env &&
          !LegacyStructs.storageMember node env)) then
      failAt node s!"Solidity 0.7.6 scalar slice does not support type {ty} in storage or members"
  if let some decl := declaration then
    let typeName := field? decl "typeName" |>.getD Json.null
    if optStr typeName "nodeType" == some "Mapping" && hasSignedType typeName &&
        (declaredMappingWidth? decl mappingValueWidth?).isNone &&
        (declaredMappingWidth? decl mappingKeyWidth?).isNone then
      failAt node "Solidity 0.7.6 signed mapping storage is outside the scalar slice"
  if kind == "BinaryOperation" then
    let left ← mType (← mField node "leftExpression")
    let right ← mType (← mField node "rightExpression")
    if (signedBitsOf left).isSome || (signedBitsOf right).isSome then
      unless (optStr node "operator").any
          (#["+", "-", "*", "/", "%", "<<", ">>", "==", "!=", "<", "<=", ">", ">="].contains ·) do
        failAt node "Solidity 0.7.6 signed operators require arithmetic, a shift or a comparison"
  if kind == "UnaryOperation" then
    if (signedBitsOf (← mType (← mField node "subExpression"))).isSome then
      unless optStr node "operator" == some "-" do
        failAt node "Solidity 0.7.6 signed unary operators require negation"
  if kind == "Assignment" then
    let target ← mField node "leftHandSide"
    let width := signedBitsOf (← mType target)
    let signedKey := ((field? target "baseExpression").bind (field? · "typeDescriptions") >>=
      (optStr · "typeString")).any (·.startsWith "mapping(int")
    if signedKey || (optStr node "operator" == some "=" &&
        width.any (fun w => directMappingAccess target w env)) then
      unless LegacyStructs.totalArgument (← mField target "indexExpression") true &&
          LegacyStructs.totalArgument (← mField node "rightHandSide") true do
        failAt node "signed mapping writes require effect-free scalar keys and values"
    if width.isSome then
      let localArithmetic := observedLocals && optStr target "nodeType" == some "Identifier" &&
        !((field? target "referencedDeclaration").bind (·.getNat?.toOption)).any env.stateVars.contains &&
        (optStr node "operator").any (#["+=", "-=", "*="].contains ·)
      unless optStr node "operator" == some "=" || localArithmetic do
        failAt node "Solidity 0.7.6 signed compound assignments are outside the scalar slice"
  if kind == "FunctionCall" && optStr node "kind" == some "typeConversion" then
    for arg in (← mArr (← mField node "arguments")) do
      let source ← mType arg
      if (signedBitsOf ty).isSome || (signedBitsOf source).isSome then
        let integer (t : String) := (signedBitsOf t).isSome ||
          (t.startsWith "uint" && (bitsOf t).isSome) || t.startsWith "int_const"
        unless integer ty && integer source do
          failAt node "Solidity 0.7.6 signed casts require integer source and target types"

end Compiler.CompilationModel.SolidityImport.LegacySigned
