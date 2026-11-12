import Compiler.SolidityImport.LegacyAbi
import Compiler.SolidityImport.LegacyBytePointers

/-! Legacy low-level STATICCALL returns an explicit success flag and a memory
bytes buffer. Source checks and ABI decoding remain ordinary later statements. -/
namespace Compiler.CompilationModel.SolidityImport.LegacyStaticCalls
open Lean

/-- Recognize only address.staticcall tuple initializers, including rejected options. -/
def applies (node : Json) : Bool :=
  let init := (field? node "initialValue").getD Json.null
  let callee := (field? init "expression").getD Json.null
  let member := if optStr callee "nodeType" == some "FunctionCallOptions" then
    (field? callee "expression").getD Json.null else callee
  optStr init "nodeType" == some "FunctionCall" &&
    optStr member "nodeType" == some "MemberAccess" &&
    optStr member "memberName" == some "staticcall" &&
    (field? member "referencedDeclaration").isNone

/-- Evaluate operands without effects, retain all returndata and use the legacy
zero-slot pointer for empty responses. Nonempty responses allocate rounded space
at the current (possibly unaligned) free pointer, without clearing trailing bytes. -/
def lower (node : Json) (leaf : Json → M Val) (bytes : Json → M EncodedBytes) :
    M (Array Stmt) := do
  unless (← get).legacyWrapping do failAt node "raw static tuples require Solidity 0.7.6"
  if (← get).legacyAbiV2Files.contains (← get).currentFile then
    failAt node "raw static tuples require ABI coder v1"
  -- The general frontend has a caller-address shortcut for some immutables.
  -- Raw calls must not inherit that substitution for an unknown deployed target.
  if (← get).stateVars.toList.any (fun (_, decl) =>
      optStr decl "mutability" == some "immutable") then
    failAt node "raw static calls require a contract without unresolved immutables"
  let init ← mField node "initialValue"
  let member ← mField init "expression"
  unless optStr member "nodeType" == some "MemberAccess" do
    failAt member "raw static call options are outside this slice"
  let base ← mField member "expression"
  unless ["address", "address payable"].contains (← mType base) do
    failAt base "raw static call requires an address receiver"
  let clean := fun arg => do
    let value ← leaf arg
    unless value.pre.isEmpty do failAt arg "raw static operands must be effect-free"
    pure value
  let target ← atom (← clean base)
  let arguments ← mArr (← mField init "arguments")
  let names ← mArr (← mField init "names")
  unless arguments.size == 1 && names.isEmpty do
    failAt init "raw static call requires one unnamed bytes argument"
  let input ← if LegacyAbi.isSelectorEncoding arguments[0]! then
    LegacyAbi.lower arguments[0]! clean
    else if optStr arguments[0]! "nodeType" == some "Identifier" &&
        (← mType arguments[0]!) == "bytes memory" then bytes arguments[0]!
    else failAt init "raw static input requires selector encoding or existing memory bytes"
  let declarations ← mArr (← mField node "declarations")
  unless declarations.size == 2 && declarations.all (!·.isNull) do
    failAt node "raw static call requires a bool and memory bytes tuple"
  let success := declarations[0]!
  let data := declarations[1]!
  unless (← mType success) == "bool" && (← mType data) == "bytes" &&
      optStr data "storageLocation" == some "memory" do
    failAt node "raw static call requires a bool and memory bytes tuple"
  let sid ← mNat (← mField success "id")
  let sname ← mStr (← mField success "name")
  let result ← freshFor sname
  let did ← mNat (← mField data "id")
  let dname ← mStr (← mField data "name")
  modify fun e => { e with
    values := e.values.insert sid (.localVar result), scalarTy := e.scalarTy.insert sid .bool
    writableLocals := e.writableLocals.insert sid result
    yulNames := e.yulNames.insert sname (.localVar result), encodingMemory := true }
  let mut pre := target.pre ++ input.pre
  let mut gas := Expr.literal (2^256 - 1)
  if (← get).sourceGas then
    let observed ← fresh
    let site ← mStr (← mField init "src")
    pre := pre.push (.ecm (Compiler.ECM.SourceGasRead.module observed site) [])
    gas := .localVar observed
  let headerName ← fresh
  let sizeName ← fresh
  let header := Expr.localVar headerName
  let size := Expr.localVar sizeName
  let capacity := Expr.bitAnd (.add size (.literal 31)) (.bitNot (.literal 31))
  pre := pre ++ #[.ecm (Compiler.ECM.SolidityRawStaticCall.module result)
    [gas, target.expr, input.pointer, input.size],
    .letVar headerName (.literal 96), .letVar sizeName .returndataSize,
    .ite (.gt size (.literal 0)) [
      .assignVar headerName (.mload (.literal 64)),
      .mstore (.literal 64) (.add (.add header (.literal 32)) capacity),
      .mstore header size,
      .returndataCopy (.add header (.literal 32)) (.literal 0) size] []]
  let bound ← LegacyBytePointers.bind did dname
    { pre := #[], pointer := .add header (.literal 32), size }
  return pre ++ bound

end Compiler.CompilationModel.SolidityImport.LegacyStaticCalls
