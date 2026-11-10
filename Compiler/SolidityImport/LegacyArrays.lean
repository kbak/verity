import Compiler.SolidityImport.ExprHelpers
import Compiler.SolidityImport.AbiLowering

/-! ABI-v1 memory address arrays with statically guarded reads. No allocation,
array mutation, unguarded indexing, or exceptional-halt semantics are admitted. -/

open Lean
namespace Compiler.CompilationModel.SolidityImport.LegacyArrays

private def child (node : Json) (key : String) : Json :=
  field? node key |>.getD Json.null

private def identifier? (node : Json) : Option Nat := do
  unless optStr node "nodeType" == some "Identifier" do none
  (field? node "referencedDeclaration").bind (·.getNat?.toOption)

private def lengthArray? (node : Json) : Option Nat := do
  unless optStr node "nodeType" == some "MemberAccess" &&
      optStr node "memberName" == some "length" do none
  let base := child node "expression"
  unless ((field? base "typeDescriptions").bind (optStr · "typeString")) ==
      some "address[] memory" do none
  identifier? base

private partial def rejectWrite (target : Json) : M Unit := do
  if optStr target "nodeType" == some "TupleExpression" then
    for item in (← mArr (← mField target "components")) do
      unless item.isNull do rejectWrite item
  else
    if (← mType target).startsWith "address[]" then
      failAt target "Solidity 0.7.6 address-array writes are outside the guarded-read slice"
    if optStr target "nodeType" == some "IndexAccess" then
      if (← mType (child target "baseExpression")) == "address[] memory" then
        failAt target "Solidity 0.7.6 address-array writes are outside the guarded-read slice"

private partial def validate (node : Json) (writes : List Nat)
    (aliases : Std.HashMap Nat Nat) (bounds : List (Nat × Nat)) : M Unit := do
  if optStr node "nodeType" == some "Block" then
    let mut aliases := aliases
    for stmt in (← mArr (← mField node "statements")) do
      validate stmt writes aliases bounds
      if optStr stmt "nodeType" == some "VariableDeclarationStatement" then
        if let some array := lengthArray? (child stmt "initialValue") then
          let decls ← mArr (← mField stmt "declarations")
          if let some decl := decls[0]? then
            if let some id := (field? decl "id").bind (·.getNat?.toOption) then
              unless writes.contains id || writes.contains array do
                aliases := aliases.insert id array
    return
  if optStr node "nodeType" == some "ForStatement" then
    -- The common exact-loop lowerer independently checks zero start, unit step,
    -- invariant bound, and no body assignment to the unsigned counter.
    let cond := child node "condition"
    validate (child node "initializationExpression") writes aliases bounds
    validate cond writes aliases bounds
    validate (child node "loopExpression") writes aliases bounds
    let rhs := child cond "rightExpression"
    let array := (lengthArray? rhs).orElse fun _ => (identifier? rhs).bind aliases.get?
    let counter := identifier? (child cond "leftExpression")
    let mut bodyBounds := bounds
    if optStr cond "operator" == some "<" then
      if let some array := array then
        if let some counter := counter then
          unless writes.contains array || (bodyAssignedIds (child node "body")).contains counter do
            bodyBounds := (array, counter) :: bounds
    validate (child node "body") writes aliases bodyBounds
    return
  if optStr node "nodeType" == some "IndexAccess" then
    if (← mType (child node "baseExpression")) == "address[] memory" then
      let pair := do
        let array ← identifier? (child node "baseExpression")
        let index ← identifier? (child node "indexExpression")
        pure (array, index)
      unless pair.any bounds.contains do
        failAt node "Solidity 0.7.6 address-array reads require an exact array-length loop guard"
  if optStr node "nodeType" == some "Assignment" ||
      (optStr node "nodeType" == some "UnaryOperation" &&
        #[some "++", some "--", some "delete"].contains (optStr node "operator")) then
    let target := if optStr node "nodeType" == some "Assignment" then
        child node "leftHandSide" else child node "subExpression"
    rejectWrite target
  match node with
  | .arr xs => xs.forM fun item => validate item writes aliases bounds
  | .obj fields =>
      for (_, value) in fields do validate value writes aliases bounds
  | _ => pure ()

private partial def arrayDeclarations (node : Json) : List Nat :=
  match node with
  | .arr xs => xs.toList.flatMap arrayDeclarations
  | .obj fields =>
      let own := if optStr node "nodeType" == some "VariableDeclaration" &&
          ((field? node "typeDescriptions").bind (optStr · "typeString")) ==
            some "address[]" then
          ((field? node "id").bind (·.getNat?.toOption)).toList else []
      fields.foldl (fun ids _ value => ids ++ arrayDeclarations value) own
  | _ => []

private partial def rejectAssemblyReferences (node : Json) (arrays : List Nat) : M Unit := do
  if optStr node "nodeType" == some "InlineAssembly" then
    for ref in (← mArr (← mField node "externalReferences")) do
      if arrays.contains (← mNat (← mField ref "declaration")) then
        failAt node "Solidity 0.7.6 assembly array references are outside the guarded-read slice"
    return
  match node with
  | .arr xs => xs.forM fun item => rejectAssemblyReferences item arrays
  | .obj fields =>
      for (_, value) in fields do rejectAssemblyReferences value arrays
  | _ => pure ()

/-- Establish every admitted array read's bound within the reached declaration.
Length aliases must dominate the loop and remain unassigned throughout the body.
Caller assumptions and mutable counters never justify a helper's array reads. -/
def validateDeclaration (node : Json) : M Unit := do
  rejectAssemblyReferences (child node "body") (arrayDeclarations node)
  validate (child node "body") (bodyAssignedIds (child node "body")) {} []

/-- ABI-v1 uses inclusive 32-bit offset/length limits and copies uncleaned address
words into memory. High-level reads clean them; the decoder also clears one word
at the end of the allocation, as the pinned compiler does. -/
def memoryHead
    (pointer offset header length data nextFree index : String)
    (rootHeadWords headOffset : Nat) : List Stmt :=
  let len := Expr.localVar length
  let memory := Expr.localVar pointer
  let source := Expr.localVar data
  [ AbiLowering.guard (.ge .calldatasize (.literal (4 + 32 * rootHeadWords)))
  , .letVar offset (.calldataload (.literal headOffset))
  , AbiLowering.guard (.le (.localVar offset) (.literal (2^32)))
  , .letVar header (.add (.literal 4) (.localVar offset))
  , AbiLowering.guard (.le (.add (.localVar header) (.literal 32)) .calldatasize)
  , .letVar length (.calldataload (.localVar header))
  , .letVar data (.add (.localVar header) (.literal 32))
  , AbiLowering.guard (.le len (.literal (2^32)))
  , AbiLowering.guard (.le (.add source (.mul len (.literal 32))) .calldatasize)
  , .letVar pointer (.mload (.literal 64))
  , .letVar nextFree (.add memory (.mul (.add len (.literal 1)) (.literal 32)))
  , .mstore (.literal 64) (.localVar nextFree)
  , .mstore memory len
  , .forEach index len
      [.mstore (.add (.add memory (.literal 32)) (.mul (.localVar index) (.literal 32)))
        (.calldataload (.add source (.mul (.localVar index) (.literal 32))))]
  , .mstore (.localVar nextFree) (.literal 0) ]

end Compiler.CompilationModel.SolidityImport.LegacyArrays
