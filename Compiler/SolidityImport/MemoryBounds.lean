import Compiler.SolidityImport.ExprHelpers

/-! Conservative root-level interval audit for source memory accesses. The audit
follows scalar bindings, successful guards and allocator metadata in source order.
It does not insert runtime assumptions or change the source program's behavior. -/
namespace Compiler.CompilationModel.SolidityImport.MemoryBounds
open Lean

private structure Range where
  lo : Nat := 0
  hi : Nat := 2^256 - 1
  deriving BEq, Inhabited

private structure Bounds where
  values : Std.HashMap String Range := {}
  free : Range := {}
  versions : Std.HashMap String Nat := {}
  guards : Std.HashMap String (List (String × Nat × Nat)) := {}
  accesses : Std.HashMap String MemoryAccess := {}
  seen : Std.HashSet String := {}
  deriving Inhabited

private def exact (n : Nat) : Range := ⟨n, n⟩

private def bounded (lo hi : Nat) : Range :=
  if hi < 2^256 then ⟨lo, hi⟩ else {}

private partial def evaluate (s : Bounds) : Expr → Range
  | .literal n => exact (n % 2^256)
  | .localVar name | .param name => s.values[name]?.getD {}
  | .add a b =>
      let a := evaluate s a; let b := evaluate s b
      bounded (a.lo + b.lo) (a.hi + b.hi)
  | .sub a b =>
      let a := evaluate s a; let b := evaluate s b
      if b.hi ≤ a.lo then ⟨a.lo - b.hi, a.hi - b.lo⟩ else {}
  | .mul a b =>
      let a := evaluate s a; let b := evaluate s b
      bounded (a.lo * b.lo) (a.hi * b.hi)
  | .bitAnd a b => ⟨0, min (evaluate s a).hi (evaluate s b).hi⟩
  | .mload addr => if evaluate s addr == exact 64 then s.free else {}
  | .lt .. | .le .. | .gt .. | .ge .. | .eq .. | .logicalNot .. => ⟨0, 1⟩
  | _ => {}

private def scalar (expr : Expr) : Bool :=
  expr.foldBool (fun e => match e with
    | .literal _ | .localVar _ | .param _ | .calldatasize | .calldataload _
    | .storageArrayElement _ _
    | .mload _ | .keccak256 _ _ | .add _ _ | .sub _ _ | .mul _ _
    | .div _ _ | .mod _ _ | .sdiv _ _ | .smod _ _
    | .bitAnd _ _ | .bitOr _ _ | .bitXor _ _ | .bitNot _
    | .shl _ _ | .shr _ _ | .sar _ _ | .signextend _ _ | .byte _ _
    | .lt _ _ | .le _ _ | .gt _ _ | .ge _ _ | .eq _ _
    | .slt _ _ | .sgt _ _ | .logicalAnd _ _ | .logicalOr _ _ | .logicalNot _ => false
    | _ => true) |>.not

private def key : Expr → Option String
  | .localVar name | .param name => some name
  | _ => none

private def upper (s : Bounds) (expr : Expr) (limit : Nat) : Bounds :=
  match key expr with
  | some name => { s with
      values := s.values.insert name { evaluate s expr with hi := min (evaluate s expr).hi limit } }
  | none => s

private def fact (s : Bounds) (expr : Expr) (limit : Nat) : List (String × Nat × Nat) :=
  match key expr with
  | some name => [(name, s.versions[name]?.getD 0, limit)]
  | none => []

private partial def facts (s : Bounds) : Expr → List (String × Nat × Nat)
  | .localVar name => s.guards[name]?.getD []
  | .le a b | .logicalNot (.gt a b) => fact s a (evaluate s b).hi
  | .lt a b | .logicalNot (.ge a b) => fact s a ((evaluate s b).hi - 1)
  | .ge a b | .logicalNot (.lt a b) => fact s b (evaluate s a).hi
  | .gt a b | .logicalNot (.le a b) => fact s b ((evaluate s a).hi - 1)
  | .logicalAnd a b => facts s a ++ facts s b
  | _ => []

private def assume (s : Bounds) (cond : Expr) : Bounds :=
  (facts s cond).foldl (fun s (name, version, limit) =>
    if s.versions[name]?.getD 0 == version then upper s (.localVar name) limit else s) s

private def failure (access : MemoryAccess) (reason : String) : M α := do
  modify fun e => { e with currentFile := access.file, stack := access.stack }
  failAt access.node reason

private def check (access : MemoryAccess) (range : Range) : M Unit := do
  let metadata := access.metadata && range == exact 64
  unless range.lo ≤ range.hi && (metadata ||
      (128 ≤ range.lo && range.hi + access.size ≤ 2^32)) do
    failure access "bounded memory requires nonwrapping addresses in [128, 2^32), or word 0x40"

private def terminal : List Stmt → Bool
  | [.revertEmpty] | [.revertError ..] | [.panicCode ..] | [.panic ..] => true
  | _ => false

private def failRoot (s : Bounds) (reason : String) : M α := do
  let some (_, access) := s.accesses.toList.head?
    | throwError "missing bounded-memory source access"
  failure access reason

private def unsupported (s : Bounds) : M α :=
  failRoot s "bounded memory requires a straight-line scalar root with successful guards"

private def bind (s : Bounds) (name : String) (value : Expr) : M Bounds := do
  let range := evaluate s value
  let constraints := facts s value
  let mut s := { s with
    values := s.values.insert name range
    versions := s.versions.insert name (s.versions[name]?.getD 0 + 1)
    guards := s.guards.insert name constraints }
  if let some access := s.accesses[name]? then
    check access range
    s := { s with seen := s.seen.insert name }
  return s

private def store (s : Bounds) (address value : Expr) : M Bounds := do
  let sourceWrite := match address with
    | .localVar name => s.accesses.contains name
    | .literal 64 => match value with | .literal 128 => true | _ => false
    | _ => false
  unless sourceWrite do
    failRoot s "bounded memory cannot observe synthetic allocation memory writes"
  let range := evaluate s address
  if range == exact 64 then
    let pointer := evaluate s value
    unless 128 ≤ pointer.lo && pointer.hi < 2^32 && pointer.lo ≤ pointer.hi do
      failRoot s "bounded memory requires a bounded free pointer"
    return { s with free := pointer }
  else if range.hi < 33 || 96 ≤ range.lo then return s
  else return { s with free := {} }

private def step (s : Bounds) (stmt : Stmt) : M Bounds := do
  unless stmt.directMetadata.subexpressions.all scalar do unsupported s
  match stmt with
  | .letVar name value | .assignVar name value => bind s name value
  | .require cond _ | .requireError cond _ _ => return assume s cond
  | .mstore address value => store s address value
  | .ite cond [] no =>
      unless terminal no do unsupported s
      return assume s cond
  | .return _ | .returnValues _ | .revertEmpty | .revertError ..
  | .panicCode _ | .panic _ | .stop => return s
  | _ => unsupported s

/-- Consume only an intact mapping sequence carrying fresh lowering provenance.
Its scratch footprint is [0,64); allocator metadata and bounded source buffers
are unchanged. Storage words and hash results remain unknown to interval analysis. -/
private def sequence (generated : Std.HashSet String) (s : Bounds) : List Stmt → M Bounds
  | [] => pure s
  | .mstore (.literal 0) key :: .mstore (.literal 32) baseSlot ::
      .letVar name (.keccak256 (.literal 0) (.literal 64)) :: tail => do
      unless generated.contains name do
        failRoot s "bounded memory cannot observe synthetic allocation memory writes"
      unless scalar key && scalar baseSlot do unsupported s
      let next ← bind s name (.keccak256 (.literal 0) (.literal 64))
      sequence (generated.erase name) next tail
  | stmt :: rest => do
      let next ← step s stmt
      sequence generated next rest

/-- Validate all recorded addresses, including helper-inlined operations, against
successful guards and the actual preceding free-pointer writes. Generated mapping
scratch is admitted only as a complete ordered operation. No control-flow joins,
loops or storage writes are inferred; other roots retain a located rejection. -/
def validate (body : Array Stmt) : M Unit := do
  let env ← get
  let accesses := env.memoryAccesses
  if accesses.isEmpty then return
  if let some site := env.uncheckedAssemblyReferences[0]? then
    modify fun e => { e with currentFile := site.file, stack := site.stack }
    failAt site.node "bounded memory cannot consume unaudited narrow assembly references"
  let initial : Bounds := {
    accesses := Std.HashMap.ofList (accesses.toList.map fun access => (access.binding, access)) }
  let s ← sequence env.mappingScratchBindings initial body.toList
  for access in accesses do
    unless s.seen.contains access.binding do
      failure access "bounded-memory access is outside the supported root sequence"

end Compiler.CompilationModel.SolidityImport.MemoryBounds
