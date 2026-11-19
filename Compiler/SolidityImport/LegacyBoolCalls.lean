import Compiler.SolidityImport.LegacyMemory
import Compiler.SolidityImport.SourceGasCalls

/-! ABI-v1 scalar static queries with captured arguments and legacy scratch-memory decoding. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyBoolCalls
open Lean

/-- Resolve a scalar query to its declaration before selecting the ABI-v1 decoder. -/
private def queryDecl? (node : Json) (env : Env) : Option Json := do
  guard (optStr node "kind" == some "functionCall")
  let callee := field? node "expression" |>.getD Json.null
  let ty := (field? callee "typeDescriptions").bind (optStr · "typeString") |>.getD ""
  guard ((ty.splitOn " external").length > 1)
  let id ← (← field? callee "referencedDeclaration").getNat?.toOption
  env.funs.find? id

private def singleResult? (decl : Json) : Option String := do
  let parameters ← (← field? (← field? decl "returnParameters") "parameters").getArr?.toOption
  guard (parameters.size == 1)
  optStr (← field? parameters[0]! "typeDescriptions") "typeString"

/-- Recognize a resolved external view/pure declaration returning one bool. -/
def applies (node : Json) (env : Env) : Bool := (queryDecl? node env).any fun decl =>
  #[some "view", some "pure"].contains (optStr decl "stateMutability") &&
    singleResult? decl == some "bool"

/-- Only a resolved zero-argument interface view can use the address result decoder. -/
def addressQuery (node : Json) (env : Env) : Bool := (do
  let decl ← queryDecl? node env
  let id ← (← field? decl "id").getNat?.toOption
  let owner ← env.funContractId.find? id
  let params ← (← field? (← field? decl "parameters") "parameters").getArr?.toOption
  return env.contractKinds.find? owner == some "interface" && params.isEmpty &&
    optStr decl "stateMutability" == some "view" && singleResult? decl == some "address"
  : Option Bool).getD false

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

/-- Call the legacy scalar transport, whose physical output word retains all response bits. -/
def lower (node decl : Json) (scalar : Json → M Val) : M Val := do
  let env ← get
  let addressResult := addressQuery node env
  let resultType := if addressResult then "address" else "bool"
  if env.legacyAbiV2Files.contains env.currentFile then
    failAt node s!"legacy {resultType} calls require ABI coder v1 at the call site"
  if addressResult then
    if env.sourceGas then
      failAt node "legacy address queries require the gas-independent call profile"
    unless env.admittedInterfaceCalls.contains (← mNat (← mField node "id")) do
      failAt node "legacy address queries require a whole scalar binding or a guarded equality"
  let callee ← mField node "expression"
  let base ← mField callee "expression"
  unless optStr base "kind" == some "typeConversion" do
    failAt base s!"legacy {resultType} call requires an explicit interface conversion"
  let receiver ← mArr (← mField base "arguments")
  unless receiver.size == 1 && #["address", "address payable"].contains (← mType receiver[0]!) do
    failAt base s!"legacy {resultType} call receiver requires an address"
  let params ← mArr (← mField (← mField decl "parameters") "parameters")
  let args ← mArr (← mField node "arguments")
  unless args.size == params.size do failAt node "legacy bool argument count differs"
  let some hex := optStr decl "functionSelector" | failAt callee "legacy bool selector missing"
  let some selector := Compiler.Hex.parseHexNat? ("0x" ++ hex)
    | failAt callee "legacy bool selector invalid"
  unless hex.length == 8 do failAt callee "legacy bool selector length invalid"
  let target ← scalar receiver[0]!
  unless target.pre.isEmpty do failAt base s!"legacy {resultType} receiver must be effect-free"
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
  let mod ← SourceGasCalls.module node result (.bool selector params.size)
  let call := Stmt.ecm mod values
  if addressResult then
    -- The normalised bool binding is unused. The closed transport writes the exact
    -- output word at its entry free pointer. Capture that pointer before the call.
    let pointer ← fresh
    let addr := LegacyMemory.cleanScalar .address (.mload (.localVar pointer))
    return { pre := #[.letVar pointer (.mload (.literal 64)), call, .assignVar result addr],
             expr := .localVar result }
  return { pre := #[call], expr := .localVar result }

end Compiler.CompilationModel.SolidityImport.LegacyBoolCalls
