import Verity.Core.Model.Yul.Ast

/-! Closed ABI-v1 calls without return values. Calldata is scratch memory at the
free pointer; successful return bytes are ignored and the pointer is not advanced. -/
namespace Compiler.Yul.LegacyVoidCalls

/-- A scalar word, a memory payload pointer, or a calldata offset/length pair. -/
inductive Argument where
  | word
  | memoryBytes
  | calldataBytes
  deriving DecidableEq, Repr

/-- Number of scalar operands consumed by the transport, including its target. -/
def arity (layout : List Argument) : Nat :=
  1 + (layout.map fun arg => if arg == .calldataBytes then 2 else 1).sum

private def names : YulExpr → List String
  | .ident name => [name]
  | .call _ args => args.flatMap names
  | _ => []

private def add (p : YulExpr) (n : Nat) : YulExpr := .call "add" [p, .lit n]
private def store (p v : YulExpr) : YulStmt := .exprStmt (.call "mstore" [p, v])

/-- Match legacy tuple encoding in declaration order, including aliased memory
headers and overlapping copies. No output area or return-value decoder is used. -/
def compile (selector : Nat) (layout : List Argument) (args : List YulExpr) :
    Except String (List YulStmt) := do
  unless selector < 2^32 && args.length == arity layout do
    throw "legacy void call selector or argument count differs"
  let stem := "__legacy_void_" ++ String.ofList (List.replicate
    ((args.flatMap names).foldl (fun n s => max n s.length) 0 + 1) '_')
  let name := fun suffix => stem ++ suffix
  let ident := fun suffix => YulExpr.ident (name suffix)
  let bindings := args.zipIdx.map fun (arg, i) => YulStmt.let_ (name ("arg" ++ toString i)) arg
  let values := args.zipIdx.map fun (_, i) => ident ("arg" ++ toString i)
  let target := values.getD 0 (.lit 0)
  let ptr := ident "ptr"
  let tail := ident "tail"
  let mut body := bindings ++ [
    .let_ (name "ptr") (.call "mload" [.lit 64]),
    store ptr (.lit (selector * 2^224)),
    .let_ (name "tail") (add ptr (4 + 32 * layout.length))]
  let mut operand := 1
  -- Legacy ABI-v1 fills every scalar head before any dynamic offset or payload.
  for (kind, index) in layout.zipIdx do
    if kind == .word then
      body := body ++ [store (add ptr (4 + 32 * index)) (values.getD operand (.lit 0))]
    operand := operand + (if kind == .calldataBytes then 2 else 1)
  operand := 1
  for (kind, index) in layout.zipIdx do
    let head := add ptr (4 + 32 * index)
    let data := values.getD operand (.lit 0)
    if kind != .word then
      let size := ident ("size" ++ toString index)
      let rounded := ident ("rounded" ++ toString index)
      let idx := ident ("idx" ++ toString index)
      let length := if kind == .calldataBytes then values.getD (operand+1) (.lit 0)
        else .call "mload" [.call "sub" [data, .lit 32]]
      body := body ++ [store head (.call "sub" [tail, add ptr 4]),
        .let_ (name ("size" ++ toString index)) length, store tail size]
      if kind == .memoryBytes then
        -- The copy reloads the length after writing the outgoing length word.
        body := body ++ [.assign (name ("size" ++ toString index)) length]
      body := body ++ [.let_ (name ("rounded" ++ toString index))
        (.call "and" [add size 31, .call "not" [.lit 31]])]
      if kind == .calldataBytes then
        body := body ++ [.exprStmt (.call "calldatacopy" [add tail 32, data, size]),
          store (.call "add" [add tail 32, size]) (.lit 0)]
      else
        let last := YulExpr.call "add" [tail, rounded]
        body := body ++ [
          .for_ [.let_ (name ("idx" ++ toString index)) (.lit 0)] (.call "lt" [idx, size])
            [.assign (name ("idx" ++ toString index)) (add idx 32)]
            [store (.call "add" [add tail 32, idx]) (.call "mload" [.call "add" [data, idx]])],
          .if_ (.call "and" [size, .lit 31]) [store last (.call "and" [
            .call "mload" [last], .call "not" [.call "sub" [
              .call "exp" [.lit 256, .call "sub" [rounded, size]], .lit 1]]])]]
      body := body ++ [.assign (name "tail") (.call "add" [add tail 32, rounded])]
    operand := operand + (if kind == .calldataBytes then 2 else 1)
  body := body ++ [
    .if_ (.call "iszero" [.call "extcodesize" [target]])
      [.exprStmt (.call "revert" [.lit 0, .lit 0])],
    .let_ (name "success") (.call "call" [.call "gas" [], target, .lit 0,
      ptr, .call "sub" [tail, ptr], .lit 0, .lit 0]),
    .if_ (.call "iszero" [ident "success"]) [
      .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, .call "returndatasize" []]),
      .exprStmt (.call "revert" [.lit 0, .call "returndatasize" []])]]
  return [.block body]

end Compiler.Yul.LegacyVoidCalls
