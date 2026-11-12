import Verity.Core.Model.Yul.Ast

/-! Closed Solidity 0.7.6 ABI-v1 static calls returning bool. The legacy decoder
accepts every nonzero word; input/output scratch memory stays at the free pointer. -/
namespace Compiler.Yul.LegacyBoolCalls

private def names : YulExpr → List String
  | .ident name => [name]
  | .call _ args => args.flatMap names
  | _ => []

/-- Capture scalar operands, check code, and preserve exact failure/response bytes.
Only the decoded value is normalized; the physical output word remains unchanged. -/
def compile (result : String) (selector count : Nat) (args : List YulExpr) :
    Except String (List YulStmt) := do
  unless selector < 2^32 && args.length == count + 1 do
    throw "legacy bool call selector or argument count differs"
  let stem := "__legacy_bool_" ++ toString result.length ++ "_" ++ result ++ "_" ++
    String.ofList (List.replicate
    ((result :: args.flatMap names).foldl (fun n s => max n s.length) 0 + 1) '_')
  let ident := fun suffix => YulExpr.ident (stem ++ suffix)
  let bindings := args.zipIdx.map fun (arg, i) =>
    YulStmt.let_ (stem ++ "arg" ++ toString i) arg
  let target := ident "arg0"
  let ptr := ident "ptr"
  let stores := (List.range count).map fun i => YulStmt.exprStmt (.call "mstore" [
    .call "add" [ptr, .lit (4 + i * 32)], ident ("arg" ++ toString (i+1))])
  return bindings ++ [.let_ result (.lit 0), .block (
    [.let_ (stem ++ "ptr") (.call "mload" [.lit 64]),
     .exprStmt (.call "mstore" [ptr, .lit (selector * 2^224)])] ++ stores ++ [
     .if_ (.call "iszero" [.call "extcodesize" [target]])
       [.exprStmt (.call "revert" [.lit 0, .lit 0])],
     .let_ (stem ++ "success") (.call "staticcall" [
       .call "gas" [], target, ptr, .lit (4 + count * 32), ptr, .lit 32]),
     .if_ (.call "iszero" [ident "success"]) [
       .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, .call "returndatasize" []]),
       .exprStmt (.call "revert" [.lit 0, .call "returndatasize" []])],
     .if_ (.call "lt" [.call "returndatasize" [], .lit 32])
       [.exprStmt (.call "revert" [.lit 0, .lit 0])],
     .assign result (.call "iszero" [.call "iszero" [.call "mload" [ptr]]])])]

end Compiler.Yul.LegacyBoolCalls
