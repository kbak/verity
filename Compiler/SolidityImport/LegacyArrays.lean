import Compiler.SolidityImport.ExprHelpers
import Compiler.SolidityImport.AbiLowering

/-! ABI-v1 address arrays: legacy decoding, allocation, indexed memory access,
and ABI returns. Reference rebinding and assembly access remain excluded. -/

open Lean
namespace Compiler.CompilationModel.SolidityImport.LegacyArrays

private def child (node : Json) (key : String) : Json :=
  field? node key |>.getD Json.null

private partial def validateTarget (target : Json) (inTuple : Bool := false) : M Unit := do
  if optStr target "nodeType" == some "TupleExpression" then
    for item in (← mArr (← mField target "components")) do
      unless item.isNull do validateTarget item true
  else
    if (← mType target).startsWith "address[]" then
      failAt target "Solidity 0.7.6 address-array reference writes are unsupported"
    if inTuple && optStr target "nodeType" == some "IndexAccess" then
      if (← mType (child target "baseExpression")) == "address[] memory" then
        failAt target "Solidity 0.7.6 tuple address-array writes are unsupported"

private partial def validateWrites (node : Json) : M Unit := do
  if optStr node "nodeType" == some "Assignment" ||
      (optStr node "nodeType" == some "UnaryOperation" &&
        #[some "++", some "--", some "delete"].contains (optStr node "operator")) then
    let target := child node (if optStr node "nodeType" == some "Assignment" then
      "leftHandSide" else "subExpression")
    validateTarget target
  if optStr node "nodeType" == some "VariableDeclarationStatement" then
    for decl in (← mArr (← mField node "declarations")) do
      unless decl.isNull do
        if (← mType decl) == "address[]" && (child node "initialValue").isNull then
          failAt node "Solidity 0.7.6 address-array locals require an explicit initializer"
  match node with
  | .arr xs => xs.forM validateWrites
  | .obj fields => for (_, value) in fields do validateWrites value
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
        failAt node "Solidity 0.7.6 assembly array references are outside the supported memory-array subset"
    return
  match node with
  | .arr xs => xs.forM fun item => rejectAssemblyReferences item arrays
  | .obj fields =>
      for (_, value) in fields do rejectAssemblyReferences value arrays
  | _ => pure ()

/-- Keep memory lengths stable and prevent assembly aliases from bypassing the
address cleanup and allocation rules. Every index has a runtime INVALID guard. -/
def validateDeclaration (node : Json) : M Unit := do
  rejectAssemblyReferences (child node "body") (arrayDeclarations node)
  validateWrites (child node "body")

/-- Exact out-of-bounds failure in the pre-0.8 compiler. -/
def invalid : Stmt := .ecm Compiler.ECM.SolidityInvalid.module []

/-- Legacy allocation bounds the element count, with empty REVERT on overflow.
Unlike modern allocation it does not check a 64-bit end pointer or emit Panic. -/
def allocate (length pointer nextFree index : String) : List Stmt :=
  let len := Expr.localVar length
  let memory := Expr.localVar pointer
  [ AbiLowering.guard (.le len (.literal (2^64 - 1)))
  , .letVar pointer (.mload (.literal 64))
  , .letVar nextFree (.add memory (.mul (.literal 32) (.add len (.literal 1))))
  , .mstore memory len
  , .mstore (.literal 64) (.localVar nextFree)
  , .forEach index len
      [.mstore (.add (.add memory (.literal 32)) (.mul (.localVar index) (.literal 32)))
        (.literal 0)] ]

/-- ABI-v1 returns copy raw memory words, including dirty calldata copies.
The caller runs post-modifiers before encoding the returned memory reference. -/
def returnMemory (array : ScalarArrayParam) (output index : String) : List Stmt :=
  let pointer := Expr.localVar output
  let len := Expr.localVar array.lengthBinding
  let offset := Expr.mul (.localVar index) (.literal 32)
  [ .letVar output (.mload (.literal 64))
  , .mstore pointer (.literal 32)
  , .mstore (.add pointer (.literal 32)) len
  , .forEach index len
      [.mstore (.add (.add pointer (.literal 64)) offset)
        (.mload (.add (.add (.localVar array.memoryPointer) (.literal 32)) offset))]
  , .ecm Compiler.ECM.SolidityReturnMemory.module
      [pointer, .add (.literal 64) (.mul len (.literal 32))]
  , .revertEmpty ]

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
