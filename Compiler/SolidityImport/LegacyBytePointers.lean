import Compiler.SolidityImport.ExprHelpers

/-! Legacy memory bytes are pointers to a length word, not copied slices.
The buffer descriptor stores the data pointer; every use reloads its header. -/
namespace Compiler.CompilationModel.SolidityImport
open Lean Compiler.CompilationModel

/-- Read a legacy memory buffer's live length, including through aliases. -/
def Env.memoryByteBuffer? (env : Env) (id : Nat) : Option EncodedBytes :=
  (env.byteBuffers.find? id).map fun buffer =>
    if env.legacyWrapping then
      { buffer with size := .mload (.sub buffer.pointer (.literal 32)) }
    else buffer

namespace LegacyBytePointers

/-- Resolve an unshadowed memory-bytes identifier to its header address. -/
def header? (node : Json) : M (Option Val) := do
  let env ← get
  unless env.legacyWrapping && optStr node "nodeType" == some "YulIdentifier" do
    return none
  let name ← mStr (← mField node "name")
  if env.yulNames.contains name then return none
  let some id := env.yulMemoryStructs.find? name | return none
  let some buffer := env.memoryByteBuffer? id | return none
  return some { pre := buffer.pre, expr := .sub buffer.pointer (.literal 32) }

/-- Memory reads through bytes-rooted address expressions retain physical aliases. -/
partial def rooted (node : Json) : M Bool := do
  if (← header? node).isSome then return true
  unless optStr node "nodeType" == some "YulFunctionCall" do return false
  (← mArr (← mField node "arguments")).anyM rooted

/-- Bind a pointer value without copying bytes or eagerly reading the length. -/
def bind (id : Nat) (name : String) (buffer : EncodedBytes) : M (Array Stmt) := do
  let pointer ← freshFor (if name == "" then "bytes_pointer" else name)
  let retained : EncodedBytes := {
    pre := #[], pointer := .localVar pointer
    size := .mload (.sub (.localVar pointer) (.literal 32)) }
  modify fun env => { env with
    byteBuffers := env.byteBuffers.insert id retained
    yulNames := env.yulNames.erase name
    yulMemoryStructs := if name == "" then env.yulMemoryStructs
      else env.yulMemoryStructs.insert name id
    nonLiteralByteLocals := env.nonLiteralByteLocals.push id }
  return buffer.pre.push (.letVar pointer buffer.pointer)

/-- Rebind either a local data pointer or a root parameter's header binding. -/
def assignData (buffer : EncodedBytes) (data : Expr) (at_ : Json) : M Stmt := do
  match buffer.pointer with
  | .localVar binding => return .assignVar binding data
  | .add (.localVar binding) (.literal 32) =>
      return .assignVar binding (.sub data (.literal 32))
  | _ => failAt at_ "legacy bytes pointer target is not a mutable memory binding"

/-- Resolve the declaration and source position before assigning a bytes header.
No allocation, bounds check, or length load belongs to the pointer assignment. -/
def assign? (target : Json) (refs : Array Json) (header : Expr) : M (Option Stmt) := do
  let env ← get
  unless env.legacyWrapping do return none
  let name ← mStr (← mField target "name")
  let some id := env.yulMemoryStructs.find? name | return none
  let some buffer := env.byteBuffers.find? id | return none
  if env.yulNames.contains name then failAt target "shadowed legacy bytes pointer target"
  let src ← mStr (← mField target "src")
  let some ref := refs.find? (fun ref => optStr ref "src" == some src)
    | failAt target "unresolved legacy bytes pointer target"
  unless (← mNat (← mField ref "declaration")) == id &&
      !(← mBool (← mField ref "isOffset")) && !(← mBool (← mField ref "isSlot")) &&
      (field? ref "suffix").isNone && (← mNat (← mField ref "valueSize")) == 1 do
    failAt target "legacy bytes pointer target declaration differs"
  return some (← assignData buffer (.add header (.literal 32)) target)

end LegacyBytePointers
end Compiler.CompilationModel.SolidityImport
