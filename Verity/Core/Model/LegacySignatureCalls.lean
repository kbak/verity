import Verity.Core.Model.Yul.Ast

/-! Solidity 0.7.6 call scratch layouts. These are transports, not a
cryptographic implementation or an assumption about a contract validator. -/
namespace Compiler.Yul.LegacySignatureCalls

private def names : YulExpr → List String
  | .ident n => [n]
  | .call _ args => args.flatMap names
  | _ => []

private def scratchPrefix (result : String) (args : List YulExpr) : String :=
  "__legacy_" ++ toString result.length ++ "_" ++ result ++ "_" ++
    String.ofList (List.replicate
    ((result :: args.flatMap names).foldl (fun n s => max n s.length) 0 + 1) '_')

private def bindArguments (p : String) (args : List YulExpr) : List YulStmt × List YulExpr :=
  let pairs := args.zipIdx.map fun (arg, i) =>
    let name := p ++ "arg" ++ toString i
    (YulStmt.let_ name arg, YulExpr.ident name)
  (pairs.map Prod.fst, pairs.map Prod.snd)

private def store (p v : YulExpr) : YulStmt := .exprStmt (.call "mstore" [p, v])
private def add (p : YulExpr) (n : Nat) : YulExpr := .call "add" [p, .lit n]
private def forwardFailure (success : YulExpr) : YulStmt :=
  .if_ (.call "iszero" [success]) [
    .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, .call "returndatasize" []]),
    .exprStmt (.call "revert" [.lit 0, .call "returndatasize" []])]

/-- Reserve a zeroed result word, then encode four words at the new free pointer.
The precompile writes into the reserved word; an empty response leaves zero. -/
def recover (result : String) (args : List YulExpr) : Except String (List YulStmt) := do
  unless args.length == 4 do throw "legacy recovery expects hash, v, r, s"
  let p := scratchPrefix result args
  let (bindings, args) := bindArguments p args
  let ptr := YulExpr.ident (p ++ "ptr")
  let success := YulExpr.ident (p ++ "success")
  return bindings ++ [.let_ result (.lit 0), .block (
    [.let_ (p ++ "ptr") (.call "mload" [.lit 64]), store ptr (.lit 0),
      store (.lit 64) (add ptr 32)] ++
    args.zipIdx.map (fun (arg, i) => store (add ptr (32 + 32 * i)) arg) ++
    [.let_ (p ++ "success") (.call "staticcall"
      [.call "gas" [], .lit 1, add ptr 32, .lit 128, ptr, .lit 32]),
     forwardFailure success,
     .assign result (.call "and" [.call "mload" [ptr], .lit (2^160 - 1)])])]

/-- Encode `(bytes32, bytes)` at the free pointer without advancing it, check
code existence, forward failure bytes, require a word and clean bytes4 padding. -/
def validate (result : String) (selector : Nat) (args : List YulExpr) :
    Except String (List YulStmt) := do
  unless selector < 2^32 do throw "legacy selector exceeds four bytes"
  let p := scratchPrefix result args
  let (bindings, args) := bindArguments p args
  let [target, hash, data, size] := args
    | throw "legacy bytes4 call expects target, hash, data pointer, size"
  let ptr := YulExpr.ident (p ++ "ptr")
  let idx := YulExpr.ident (p ++ "idx")
  let rounded := YulExpr.ident (p ++ "rounded")
  let success := YulExpr.ident (p ++ "success")
  let tail := YulExpr.call "add" [add ptr 100, .call "sub" [rounded, .lit 32]]
  return bindings ++ [.let_ result (.lit 0), .block [
    .let_ (p ++ "ptr") (.call "mload" [.lit 64]),
    .let_ (p ++ "rounded") (.call "and" [.call "add" [size, .lit 31], .call "not" [.lit 31]]),
    store ptr (.lit (selector * 2^224)), store (add ptr 4) hash,
    store (add ptr 36) (.lit 64), store (add ptr 68) size,
    .for_ [.let_ (p ++ "idx") (.lit 0)] (.call "lt" [idx, size])
      [.assign (p ++ "idx") (add idx 32)]
      [store (.call "add" [add ptr 100, idx]) (.call "mload" [.call "add" [data, idx]])],
    .if_ (.call "and" [size, .lit 31])
      [store tail (.call "and" [.call "mload" [tail], .call "not" [
        .call "sub" [.call "exp" [.lit 256, .call "sub" [rounded, size]], .lit 1]]])],
    .if_ (.call "iszero" [.call "extcodesize" [target]])
      [.exprStmt (.call "revert" [.lit 0, .lit 0])],
    .let_ (p ++ "success") (.call "staticcall" [
      .call "gas" [], target, ptr, add rounded 100, ptr, .lit 32]),
    forwardFailure success,
    .if_ (.call "lt" [.call "returndatasize" [], .lit 32])
      [.exprStmt (.call "revert" [.lit 0, .lit 0])],
    .assign result (.call "and" [.call "mload" [ptr], .lit ((2^32 - 1) * 2^224)])]]

end Compiler.Yul.LegacySignatureCalls
