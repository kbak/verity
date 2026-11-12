import Compiler.SolidityImport.LegacyPacked

/-! ABI-v1 static word encoding for Solidity 0.7.6. Allocation starts at the
current free pointer, which can be unaligned after a packed encoding. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyAbi
open Lean Compiler.CompilationModel

/-- Recognize the resolved standard ABI encoding builtin. -/
def isEncoding (node : Json) : Bool := LegacyPacked.isEncoding node "encode"

/-- Selector-prefixed encoding is limited to static selectors and words. -/
def isSelectorEncoding (node : Json) : Bool := LegacyPacked.isEncoding node "encodeWithSelector"

/-- Resolve a literal or a type-qualified external function's four-byte selector. -/
def selectorValue (node : Json) (lowerScalar : Json → M Val) : M Nat := do
  if optStr node "nodeType" == some "Literal" then
    let value ← lowerScalar node
    let .literal selector := value.expr | failAt node "legacy selector requires a constant"
    unless value.pre.isEmpty && selector < 2^32 do failAt node "legacy selector exceeds four bytes"
    return selector
  unless optStr node "nodeType" == some "MemberAccess" &&
      optStr node "memberName" == some "selector" && (← mType node) == "bytes4" do
    failAt node "legacy selector requires a literal or resolved external function selector"
  let selected ← mField node "expression"
  unless optStr selected "nodeType" == some "MemberAccess" do
    failAt node "legacy selector requires a type-qualified function"
  let owner ← mField selected "expression"
  unless optStr owner "nodeType" == some "Identifier" &&
      (← mType owner).startsWith "type(contract " do
    failAt node "legacy selector requires a type-qualified function"
  let id ← refInt selected
  let env ← get
  let some declaration := if id ≥ 0 then env.funs.find? id.toNat else none
    | failAt node "legacy selector function is unresolved"
  unless #[some "external", some "public"].contains (optStr declaration "visibility") do
    failAt node "legacy selector function must be external or public"
  let some hex := optStr declaration "functionSelector"
    | failAt node "legacy selector function has no selector"
  let some selector := Compiler.Hex.parseHexNat? ("0x" ++ hex)
    | failAt node "legacy function selector is malformed"
  unless hex.length == 8 && selector < 2^32 do
    failAt node "legacy function selector exceeds four bytes"
  return selector

/-- Lower a static scalar tuple into physical memory, including its length header.
Arguments are evaluated before stores; unsigned/address/bool words are right-aligned,
fixed bytes are left-aligned. No modern allocator or alignment rounding is inserted.
ABI-v1 sites admit direct hash inputs and selector-prefixed memory locals. -/
def lower (node : Json) (lowerScalar : Json → M Val) : M EncodedBytes := do
  unless isEncoding node || isSelectorEncoding node do
    failAt node "legacy static encoding requires abi.encode or abi.encodeWithSelector"
  let env ← get
  if env.legacyAbiV2Files.contains env.currentFile then
    failAt node "legacy static encoding requires ABI coder v1 at the call site"
  let mut pre : Array Stmt := #[]
  let mut words : Array Expr := #[]
  let arguments ← mArr (← mField node "arguments")
  let selector ← if isSelectorEncoding node then do
    unless !arguments.isEmpty do failAt node "legacy selector argument missing"
    pure (some (← selectorValue arguments[0]! lowerScalar))
    else pure none
  let offset := if selector.isSome then 4 else 0
  let arguments := if selector.isSome then arguments.extract 1 arguments.size else arguments
  for arg in arguments do
    LegacyPacked.checkScalar arg "static ABI"
    let ty ← mType arg
    let mask ← if let some width := fixedBytesWidth? ty then
      pure ((2 ^ (8 * width) - 1) * 2 ^ (8 * (32 - width)))
    else if ty == "bool" then pure 0
    else if ty.startsWith "uint" || ty == "address" || ty == "address payable" ||
        ty.startsWith "contract " then do
      let some bits := bitsOf ty | failAt arg "unsupported legacy ABI scalar type"
      pure (2 ^ bits - 1)
    else if ty.startsWith "int_const " && !ty.startsWith "int_const -" then
      pure (2 ^ 256 - 1)
    else failAt arg "legacy static ABI encoding requires unsigned/address/bool/fixed-bytes scalars"
    let raw ← if optStr arg "nodeType" == some "Identifier" &&
        optStr arg "name" == some "this" then do
      unless (← refInt arg) == -28 do
        failAt arg "this does not resolve to the current contract builtin"
      pure { pre := #[], expr := Expr.contractAddress }
    else lowerScalar arg
    let value ← atom raw
    pre := pre ++ value.pre
    let cleaned := if ty == "bool" then Expr.logicalNot (.logicalNot value.expr)
      else Expr.bitAnd value.expr (.literal mask)
    words := words.push cleaned
  let headerName ← fresh
  let header := Expr.localVar headerName
  let data := Expr.add header (.literal 32)
  let size := offset + 32 * words.size
  pre := pre.push (.letVar headerName (.mload (.literal 64)))
  if let some selector := selector then
    pre := pre.push (.mstore data (.literal (selector * 2^224)))
  for (word, index) in words.zipIdx do
    pre := pre.push (.mstore (.add data (.literal (offset + 32 * index))) word)
  pre := pre ++ #[.mstore header (.literal size),
    .mstore (.literal 64) (.add data (.literal size))]
  return { pre, pointer := data, size := .literal size }

end Compiler.CompilationModel.SolidityImport.LegacyAbi
