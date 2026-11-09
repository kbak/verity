import Compiler.SolidityImport.ExprHelpers
import Compiler.Hex

/-! ABI-v1 packed encoding for Solidity 0.7.6. The legacy backend writes directly
at free-memory + 32, then installs the length and the unrounded end pointer. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyPacked
open Lean Compiler.CompilationModel

/-- Recognize the resolved builtin, independently of user-defined member names. -/
def isEncoding (node : Json) : Bool := Id.run do
  unless optStr node "nodeType" == some "FunctionCall" &&
      optStr node "kind" == some "functionCall" do return false
  let callee := field? node "expression" |>.getD Json.null
  unless optStr callee "nodeType" == some "MemberAccess" &&
      optStr callee "memberName" == some "encodePacked" do return false
  let base := field? callee "expression" |>.getD Json.null
  return optStr base "nodeType" == some "Identifier" && optStr base "name" == some "abi" &&
    ((field? base "referencedDeclaration").bind (·.getInt?.toOption)) == some (-1)

/-- Reject allocations, calls, assignments and other expressions whose evaluation
order or dirty-bit behavior needs additional legacy evidence. -/
private partial def checkScalar (node : Json) : M Unit := do
  match ← mKind node with
  | "Identifier" | "Literal" => pure ()
  | "MemberAccess" => checkScalar (← mField node "expression")
  | "FunctionCall" =>
      unless optStr node "kind" == some "typeConversion" do
        failAt node "legacy packed arguments require scalar values or conversions"
      for arg in (← mArr (← mField node "arguments")) do checkScalar arg
  | _ => failAt node "legacy packed arguments require scalar values or conversions"

/-- Parse literal payload words without allocating intermediate buffers. -/
private def literalWords (node : Json) : M (Nat × Array Expr) := do
  let some hex := optStr node "hexValue" | failAt node "missing literal byte spelling"
  unless hex.length % 2 == 0 do failAt node "invalid literal byte spelling"
  let chars := hex.toList.toArray
  let mut words := #[]
  let mut word := 0
  for index in [:chars.size] do
    let some digit := Compiler.Hex.hexCharToNat? chars[index]!
      | failAt node "invalid literal hex digit"
    word := word * 16 + digit
    if index % 64 == 63 then
      words := words.push (.literal word)
      word := 0
  if chars.size % 64 != 0 then
    words := words.push (.literal (word * 16 ^ (64 - chars.size % 64)))
  return (hex.length / 2, words)

/-- Lower a static packed schema with physical, possibly unaligned word stores.
Scalar values are evaluated before output stores. Width cleanup happens at the
encoding boundary. No intermediate buffers, word rounding or modern panic guard
is inserted. Dynamic bytes, ABI-v2 sites and effectful argument trees reject. -/
def lower (node : Json) (lowerScalar : Json → M Val) : M EncodedBytes := do
  unless isEncoding node do
    failAt node "legacy hashing requires abi.encodePacked with static arguments"
  let env ← get
  if env.legacyAbiV2Files.contains env.currentFile then
    failAt node "legacy packed encoding requires ABI coder v1 at the call site"
  let mut pre : Array Stmt := #[]
  let mut stores : Array (Nat × Expr) := #[]
  let mut size := 0
  for arg in (← mArr (← mField node "arguments")) do
    let ty ← mType arg
    if (← mKind arg) == "Literal" && ty.startsWith "literal_string " then
      let (length, words) ← literalWords arg
      for (word, index) in words.zipIdx do
        stores := stores.push (size + 32 * index, word)
      size := size + length
    else
      checkScalar arg
      let (width, leftAligned) ← if let some width := fixedBytesWidth? ty then
        pure (width, true)
      else if ty == "bool" then pure (1, false)
      else if ty.startsWith "uint" || ty == "address" || ty == "address payable" ||
          ty.startsWith "contract " then do
        let some bits := bitsOf ty | failAt arg "unsupported legacy packed scalar type"
        pure (bits / 8, false)
      else failAt arg "legacy packed encoding requires literal or fixed-width arguments"
      let value ← atom (← lowerScalar arg)
      pre := pre ++ value.pre
      let shift := 8 * (32 - width)
      let cleaned := if ty == "bool" then Expr.logicalNot (.logicalNot value.expr)
        else if leftAligned then
          Expr.bitAnd value.expr (.literal ((2 ^ (8 * width) - 1) * 2 ^ shift))
        else Expr.bitAnd value.expr (.literal (2 ^ (8 * width) - 1))
      let word := if leftAligned || width == 32 then cleaned
        else Expr.shl (.literal shift) cleaned
      stores := stores.push (size, word)
      size := size + width
  let headerName ← fresh
  let header := Expr.localVar headerName
  let data := Expr.add header (.literal 32)
  pre := pre.push (.letVar headerName (.mload (.literal 64)))
  for (offset, word) in stores do
    pre := pre.push (.mstore (.add data (.literal offset)) word)
  pre := pre ++ #[.mstore header (.literal size),
    .mstore (.literal 64) (.add data (.literal size))]
  return { pre, pointer := data, size := .literal size }

end Compiler.CompilationModel.SolidityImport.LegacyPacked
