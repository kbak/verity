import Lean
import Compiler.Hex

/-! Explicit deployment evidence for scalar immutable values. This checker compares
submitted runtime bytes with the freshly compiled template, replacing only solc's
immutable reference ranges. It does not authenticate chain state or constructors. -/
namespace Compiler.CompilationModel.SolidityImport.DeployedImmutables
open Lean

/-- A declaration identity comes from the freshly compiled target's inheritance closure. -/
structure Declaration where
  id : Nat
  source : String
  contract : String
  name : String
  solcType : String
  deriving Inhabited

private def key (source contract name : String) : String :=
  (Json.arr #[toJson source, toJson contract, toJson name]).compress

private def bytes (text : String) : Except String ByteArray := do
  unless text.startsWith "0x" do throw "hex bytes require a 0x prefix"
  let digits := (text.drop 2).toString.toList.toArray
  unless digits.size % 2 == 0 do throw "hex bytes have odd length"
  let mut out := ByteArray.empty
  for i in [:digits.size / 2] do
    let some hi := Compiler.Hex.hexCharToNat? digits[2*i]!
      | throw "invalid hex byte"
    let some lo := Compiler.Hex.hexCharToNat? digits[2*i+1]!
      | throw "invalid hex byte"
    out := out.push (UInt8.ofNat (16*hi+lo))
  return out

private def width (ty stem : String) (maximum : Nat) : Option Nat := do
  guard (ty.startsWith stem)
  let n ← (ty.drop stem.length).toString.toNat?
  guard (0 < n && n ≤ maximum && (maximum == 32 || n % 8 == 0))
  guard (ty == stem ++ toString n)
  return n

/-- Admitted patch words. Signed values can be zero-extended narrow bit patterns
or already sign-extended; solc cleans them when read. Expression admission is separate. -/
def validPatchWord (ty : String) (word : Nat) : Bool :=
  word < 2^256 &&
    if ty == "bool" then word < 2
    else if ty == "address" || ty == "address payable" || ty.startsWith "contract " then
      word < 2^160
    else if let some n := width ty "uint" 256 then word < 2^n
    else if let some n := width ty "int" 256 then
      word < 2^n || 2^256 - 2^(n-1) ≤ word
    else if let some n := width ty "bytes" 32 then word % 2^(8*(32-n)) == 0
    else false

/-- Convert a checked patch word to the scalar value seen by high-level reads. -/
def scalarWord (ty : String) (word : Nat) : Nat :=
  if let some n := width ty "int" 256 then
    let low := word % 2^n
    if low < 2^(n-1) then low else low + 2^256 - 2^n
  else word

/-- Check all submitted bindings and every runtime byte. Repeated references must
agree; absent, foreign, overlapping, truncated and non-word references reject.
Unreferenced declarations cannot acquire a value merely from their initializer. -/
def check (declarations : Array Declaration) (template : String) (references manifest : Json) :
    Except String (RBMap Nat Nat compare) := do
  unless (← (← manifest.getObjVal? "version").getNat?) == 1 do
    throw "unsupported immutable deployment version"
  let address ← bytes (← (← manifest.getObjVal? "codeAddress").getStr?)
  unless address.size == 20 do throw "codeAddress requires exactly 20 bytes"
  let runtime ← bytes (← (← manifest.getObjVal? "runtimeBytecode").getStr?)
  let mut expected ← bytes ("0x" ++ template)
  unless !expected.isEmpty && runtime.size == expected.size do
    throw "deployed runtime length differs from compiler template"
  let mut byName : Std.HashMap String Declaration := {}
  let mut byId : Std.HashMap Nat Declaration := {}
  for decl in declarations do
    let identity := key decl.source decl.contract decl.name
    if byName.contains identity || byId.contains decl.id then
      throw "ambiguous immutable declaration identity"
    byName := byName.insert identity decl
    byId := byId.insert decl.id decl
  let mut values : RBMap Nat Nat compare := RBMap.empty
  let mut patches : RBMap Nat Nat compare := RBMap.empty
  for binding in ← (← manifest.getObjVal? "bindings").getArr? do
    let identity := key
      (← (← binding.getObjVal? "source").getStr?)
      (← (← binding.getObjVal? "contract").getStr?)
      (← (← binding.getObjVal? "name").getStr?)
    let some decl := byName[identity]? | throw "unknown immutable declaration"
    if values.contains decl.id then throw "duplicate immutable binding"
    let ty ← (← binding.getObjVal? "type").getStr?
    unless ty == decl.solcType do throw "immutable binding type differs from declaration"
    let raw ← bytes (← (← binding.getObjVal? "word").getStr?)
    unless raw.size == 32 do throw "immutable binding requires exactly 32 bytes"
    let word := raw.foldl (fun n b => 256*n + b.toNat) 0
    unless validPatchWord ty word do throw "noncanonical or unsupported immutable word"
    values := values.insert decl.id (scalarWord ty word)
    patches := patches.insert decl.id word
  let mut seen : Std.HashSet Nat := {}
  let mut occupied : Std.HashSet Nat := {}
  for (idText, ranges) in ← references.getObj? do
    let some id := idText.toNat? | throw "invalid immutable reference identity"
    unless idText == toString id && byId.contains id do
      throw "foreign immutable reference identity"
    let some word := patches.find? id | throw "missing deployed immutable binding"
    let ranges ← ranges.getArr?
    if ranges.isEmpty then throw "empty immutable references"
    seen := seen.insert id
    for range in ranges do
      let start ← (← range.getObjVal? "start").getNat?
      let length ← (← range.getObjVal? "length").getNat?
      unless length == 32 && start + length ≤ expected.size do
        throw "invalid immutable reference range"
      for i in [:32] do
        let offset := start + i
        if occupied.contains offset then throw "overlapping immutable references"
        occupied := occupied.insert offset
        expected := expected.set! offset (UInt8.ofNat (word / 256^(31-i) % 256))
  for (id, _) in values do
    unless seen.contains id do throw "immutable binding has no runtime reference"
  unless expected == runtime do throw "deployed runtime does not match immutable bindings"
  return values

end Compiler.CompilationModel.SolidityImport.DeployedImmutables
