import Compiler.SolidityImport.LegacyMemory

/-! Resolved ABI-v1 bool-returning static calls with captured scalar arguments.
No newer strict bool decoder or allocator behavior is reused for legacy sources. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyBoolCalls
open Lean

/-- Recognize a resolved external view/pure declaration returning one bool. -/
def applies (node : Json) (env : Env) : Bool := Id.run do
  unless optStr node "kind" == some "functionCall" do return false
  let callee := field? node "expression" |>.getD Json.null
  let ty := (field? callee "typeDescriptions").bind (optStr · "typeString") |>.getD ""
  unless (ty.splitOn " external").length > 1 do return false
  let some id := (field? callee "referencedDeclaration").bind (·.getNat?.toOption)
    | return false
  let some decl := env.funs.find? id | return false
  let returns := ((field? decl "returnParameters").bind (field? · "parameters")).bind
    (·.getArr?.toOption) |>.getD #[]
  return #[some "view", some "pure"].contains (optStr decl "stateMutability") &&
    returns.size == 1 && ((field? returns[0]! "typeDescriptions").bind
      (optStr · "typeString")) == some "bool"

/-- Only the resolved `type(I).interfaceId` constant bypasses builtin-call checks.
The shared lowering independently validates the interface and selector inventory. -/
def interfaceId (node : Json) (env : Env) : Bool := Id.run do
  unless optStr node "nodeType" == some "MemberAccess" &&
      optStr node "memberName" == some "interfaceId" do return false
  let base := field? node "expression" |>.getD Json.null
  let callee := field? base "expression" |>.getD Json.null
  unless optStr base "nodeType" == some "FunctionCall" &&
      optStr callee "nodeType" == some "Identifier" &&
      optStr callee "name" == some "type" &&
      ((field? callee "referencedDeclaration").bind (·.getInt?.toOption)).any (· < 0) do
    return false
  let args := ((field? base "arguments").bind (·.getArr?.toOption)).getD #[]
  unless args.size == 1 do return false
  let some id := (field? args[0]! "referencedDeclaration").bind (·.getNat?.toOption)
    | return false
  return env.contractKinds.find? id == some "interface"

/-- Encode effect-free scalars into one closed static transport. -/
def lower (node decl : Json) (scalar : Json → M Val) : M Val := do
  let env ← get
  if env.legacyAbiV2Files.contains env.currentFile then
    failAt node "legacy bool calls require ABI coder v1 at the call site"
  let callee ← mField node "expression"
  let base ← mField callee "expression"
  unless optStr base "kind" == some "typeConversion" do
    failAt base "legacy bool call requires an explicit interface conversion"
  let receiver ← mArr (← mField base "arguments")
  unless receiver.size == 1 && #["address", "address payable"].contains (← mType receiver[0]!) do
    failAt base "legacy bool call receiver requires an address"
  let params ← mArr (← mField (← mField decl "parameters") "parameters")
  let args ← mArr (← mField node "arguments")
  unless args.size == params.size do failAt node "legacy bool argument count differs"
  let some hex := optStr decl "functionSelector" | failAt callee "legacy bool selector missing"
  let some selector := Compiler.Hex.parseHexNat? ("0x" ++ hex)
    | failAt callee "legacy bool selector invalid"
  unless hex.length == 8 do failAt callee "legacy bool selector length invalid"
  let target ← scalar receiver[0]!
  unless target.pre.isEmpty do failAt base "legacy bool receiver must be effect-free"
  let mut values := [LegacyMemory.cleanScalar .address target.expr]
  for (param, arg) in params.zip args do
    let ty ← mType param
    let argTy ← mType arg
    unless ty == argTy || (#["address", "address payable"].contains ty &&
        #["address", "address payable"].contains argTy) do
      failAt arg "legacy bool arguments require their declared scalar type"
    let some scalarTy := paramType ty | failAt arg "unsupported legacy bool argument type"
    unless #["uint256", "address", "address payable", "bool"].contains ty ||
        (fixedBytesWidth? ty).isSome do
      failAt arg "legacy bool calls require unsigned words, addresses, bools or fixed bytes"
    let value ← scalar arg
    unless value.pre.isEmpty do failAt arg "legacy bool arguments must be effect-free"
    let word := match scalarTy with
      | .bytesN width => .bitAnd value.expr (.literal ((2^(8*width)-1) * 2^(256-8*width)))
      | _ => LegacyMemory.cleanScalar scalarTy value.expr
    values := values ++ [word]
  let result ← fresh
  modify fun e => { e with encodingMemory := true }
  return { pre := #[.ecm (Compiler.ECM.LegacyBoolCall.module result selector params.size) values]
           expr := .localVar result }

end Compiler.CompilationModel.SolidityImport.LegacyBoolCalls
