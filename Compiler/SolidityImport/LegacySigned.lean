import Compiler.SolidityImport.ExprHelpers

/-! Bounded admission of legacy signed scalar arithmetic. Division, storage and
assembly need separate legacy semantics; admitting a scalar type does not admit
those uses. All arithmetic here reuses the wrapping expression lowering. -/
namespace Compiler.CompilationModel.SolidityImport.LegacySigned
open Lean

/-- Inspect mapping key/value types without expanding unrelated struct layouts. -/
private partial def hasSignedType (node : Json) : Bool :=
  ((field? node "typeDescriptions").bind (optStr · "typeString")).any
    (fun ty => (signedBitsOf ty).isSome) ||
  (optStr node "nodeType" == some "Mapping" &&
    #["keyType", "valueType"].any (fun key => (field? node key).any hasSignedType))

/-- Signed legacy scalars are admitted only in evaluated integer expressions. -/
def validate (node : Json) : M Unit := do
  let kind := optStr node "nodeType" |>.getD ""
  let ty := (field? node "typeDescriptions").bind (optStr · "typeString") |>.getD ""
  let ref := (field? node "referencedDeclaration").bind (·.getNat?.toOption)
  let env ← get
  let declaration :=
    if (field? node "stateVariable").any (fun x => x.getBool?.toOption == some true) then
      some node else ref.bind env.stateVars.find?
  if (signedBitsOf ty).isSome then
    if declaration.isSome || #["MemberAccess", "IndexAccess"].contains kind then
      failAt node s!"Solidity 0.7.6 scalar slice does not support type {ty} in storage or members"
  if let some decl := declaration then
    let typeName := field? decl "typeName" |>.getD Json.null
    if optStr typeName "nodeType" == some "Mapping" && hasSignedType typeName then
      failAt node "Solidity 0.7.6 signed mapping storage is outside the scalar slice"
  if kind == "BinaryOperation" then
    let left ← mType (← mField node "leftExpression")
    let right ← mType (← mField node "rightExpression")
    if (signedBitsOf left).isSome || (signedBitsOf right).isSome then
      unless (optStr node "operator").any
          (#["+", "-", "*", "==", "!=", "<", "<=", ">", ">="].contains ·) do
        failAt node "Solidity 0.7.6 signed operators require arithmetic or a comparison"
  if kind == "UnaryOperation" then
    if (signedBitsOf (← mType (← mField node "subExpression"))).isSome then
      unless optStr node "operator" == some "-" do
        failAt node "Solidity 0.7.6 signed unary operators require negation"
  if kind == "Assignment" then
    if (signedBitsOf (← mType (← mField node "leftHandSide"))).isSome then
      unless optStr node "operator" == some "=" do
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
