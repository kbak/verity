import Compiler.SolidityImport.LegacyPacked

/-! ABI-v1 static word encoding for Solidity 0.7.6. Allocation starts at the
current free pointer, which can be unaligned after a packed encoding. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyAbi
open Lean Compiler.CompilationModel

/-- Recognize the resolved standard ABI encoding builtin. -/
def isEncoding (node : Json) : Bool := LegacyPacked.isEncoding node "encode"

/-- Lower a static scalar tuple into physical memory, including its length header.
Arguments are evaluated before stores; unsigned/address/bool words are right-aligned,
fixed bytes are left-aligned. No modern allocator or alignment rounding is inserted.
Only direct hash inputs at ABI-v1 sites are admitted by the declaration boundary. -/
def lower (node : Json) (lowerScalar : Json → M Val) : M EncodedBytes := do
  unless isEncoding node do failAt node "legacy static encoding requires abi.encode"
  let env ← get
  if env.legacyAbiV2Files.contains env.currentFile then
    failAt node "legacy static encoding requires ABI coder v1 at the call site"
  let mut pre : Array Stmt := #[]
  let mut words : Array Expr := #[]
  for arg in (← mArr (← mField node "arguments")) do
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
  let size := 32 * words.size
  pre := pre.push (.letVar headerName (.mload (.literal 64)))
  for (word, index) in words.zipIdx do
    pre := pre.push (.mstore (.add data (.literal (32 * index))) word)
  pre := pre ++ #[.mstore header (.literal size),
    .mstore (.literal 64) (.add data (.literal size))]
  return { pre, pointer := data, size := .literal size }

end Compiler.CompilationModel.SolidityImport.LegacyAbi
