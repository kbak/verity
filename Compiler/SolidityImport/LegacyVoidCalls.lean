import Compiler.SolidityImport.LegacyMemory
import Compiler.SolidityImport.LegacyBytePointers

/-! Resolved ABI-v1 interface calls with no returned values. Their arguments are
captured scalars and existing byte buffers; arbitrary argument effects and implicit
calldata-to-memory conversions remain outside this boundary. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyVoidCalls
open Lean

/-- The early legacy gate resolves a nonpayable, external, void declaration.
Detailed receiver and argument validation remains in `lower`. -/
def applies (node : Json) (env : Env) : Bool := Id.run do
  unless optStr node "kind" == some "functionCall" do return false
  let callee := field? node "expression" |>.getD Json.null
  let ty := (field? callee "typeDescriptions").bind (optStr · "typeString") |>.getD ""
  unless (ty.splitOn " external").length > 1 do return false
  let some id := (field? callee "referencedDeclaration").bind (·.getNat?.toOption)
    | return false
  let some decl := env.funs.find? id | return false
  return optStr decl "stateMutability" == some "nonpayable" &&
    ((field? decl "returnParameters").bind (field? · "parameters")).bind
      (·.getArr?.toOption) == some #[]

/-- Build one closed void transport without introducing public memory effects
between calls. Every buffer remains a physical pointer or calldata descriptor. -/
def lower (node decl : Json) (scalar : Json → M Val) : M Val := do
  let env ← get
  if env.legacyAbiV2Files.contains env.currentFile then
    failAt node "legacy void callbacks require ABI coder v1 at the call site"
  let callee ← mField node "expression"
  let base ← mField callee "expression"
  unless optStr base "kind" == some "typeConversion" do
    failAt base "legacy void callback requires an explicit interface conversion"
  let receiver ← mArr (← mField base "arguments")
  unless receiver.size == 1 && #["address", "address payable"].contains (← mType receiver[0]!) do
    failAt base "legacy void callback receiver requires an address"
  let params ← mArr (← mField (← mField decl "parameters") "parameters")
  let args ← mArr (← mField node "arguments")
  unless args.size == params.size do failAt node "legacy void callback argument count differs"
  let some hex := optStr decl "functionSelector" | failAt callee "callback selector missing"
  let some selector := Compiler.Hex.parseHexNat? ("0x" ++ hex)
    | failAt callee "callback selector invalid"
  unless hex.length == 8 do failAt callee "callback selector length invalid"
  let target ← scalar receiver[0]!
  unless target.pre.isEmpty do failAt base "callback receiver must be an effect-free scalar"
  let mut values := [LegacyMemory.cleanScalar .address target.expr]
  let mut layout : List Compiler.Yul.LegacyVoidCalls.Argument := []
  let mut pre : Array Stmt := #[]
  for (param, arg) in params.zip args do
    let ty ← mType param
    let argTy ← mType arg
    if ty == "bytes" then
      unless optStr arg "nodeType" == some "Identifier" do
        failAt arg "callback bytes require an existing buffer identifier"
      let id ← refInt arg
      if argTy == "bytes memory" then
        let some buffer := env.memoryByteBuffer? id.toNat
          | failAt arg "unknown callback memory buffer"
        unless buffer.pre.isEmpty do failAt arg "effectful callback memory buffer"
        layout := layout ++ [.memoryBytes]
        values := values ++ [buffer.pointer]
      else if argTy == "bytes calldata" then
        let some buffer := env.calldataBytes.find? id.toNat
          | failAt arg "unknown callback calldata buffer"
        if buffer.inMemory then failAt arg "callback calldata must retain its source location"
        layout := layout ++ [.calldataBytes]
        values := values ++ [.localVar buffer.dataBinding, .localVar buffer.lengthBinding]
      else failAt arg "callback bytes require memory or calldata"
    else
      unless ty == argTy || (#["address", "address payable"].contains ty &&
          #["address", "address payable"].contains argTy) do
        failAt arg "callback scalars require their declared type"
      let value ← scalar arg
      unless value.pre.isEmpty do failAt arg "callback scalar arguments must be effect-free"
      if ty.startsWith "enum " then
        let checked ← LegacyMemory.checkedEnum arg ty value
        pre := pre ++ checked.pre
        values := values ++ [checked.expr]
      else
        let some scalarTy := paramType ty | failAt arg "unsupported callback scalar type"
        unless #["uint256", "bytes32", "address", "address payable", "bool"].contains ty do
          failAt arg "callback scalar type requires additional ABI-v1 encoding support"
        values := values ++ [LegacyMemory.cleanScalar scalarTy value.expr]
      layout := layout ++ [.word]
  modify fun e => { e with encodingMemory := true }
  return {
    pre := pre.push (.ecm (Compiler.ECM.LegacyVoidCall.module selector layout) values)
    expr := .literal 0 }

end Compiler.CompilationModel.SolidityImport.LegacyVoidCalls
