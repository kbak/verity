# Full-cleanup packed hash and storage read

This is regression preparation and a proposed design for #32, based on fork PR
#43. Importer admission must remain unchanged until #39 merges and its required
gates pass. This preparation does not implement the design or complete #32.

## Executable boundary

`Contracts/SolidityImportSmoke/PackedStorageRead.sol` separates three roots:

| Root or variant | Evidence required by this preparation |
| --- | --- |
| `digest` with full cleanup | All 54 existing packed vectors agree across source EVM, actual Denote and generated Cancun EVM. |
| `readKey` with a supplied key | Six initial reads agree across those same three routes. |
| Combined `read`, helper rename, shifted layout | Six source reads each match the independent oracle; each import retains the synthetic-memory-write rejection. |
| Wrong mapping base, shortened hash | Real source execution must disagree only in return data; failures or state corruption do not count as detection. |
| Partial cleanup, dirty hash, dirty word read, unknown cleanup alias | Source-valid roots retain their respective located rejections. |
| ABI allocation before the hash | Retains the synthetic-memory-write rejection. |
| Raw scratch read after lookup | Retains the existing `unsupported Yul builtin mload` rejection. |

Full cleanup clears all three words starting at the saved free pointer after
computing the unchanged 58-byte packed hash. This is a separate generic control;
the original `PackedStorageReference.sol` and its tail-only cleanup are unchanged.

The campaign archives the complete, unchanged state expectations for both layouts
and the complete packed expectations, checking the frozen SHA-256 values from
#42/#43. It selects the original first six transactions and expected observations
without rewriting either. These reads include three seeded and three empty
records, uint128 padding, adjacent slots, other keys and enclosing sentinels.
The shifted layout retains the existing independently specified mapping base.
The supplied-key control changes only function/selector/argument inputs, and is
reported separately from the rejected combined root.

Source reads use the existing cumulative discovery/replay slot plan. Unexpected
slots must retain their initial values; missing observations or tool failures
cannot pass. Model controls use the actual imported model and generated Yul;
implementation identities, compiler/settings, deployments and observations are
retained. Pure hash controls execute with empty initial storage; stateful read
controls install the independently specified initial storage. These are finite
experiments, not constructor, balance/nonce, gas or whole-world equivalence.

## Why the combined root is rejected

The mapping-to-struct path in
[`Import.lean`](../Compiler/SolidityImport/Import.lean), `lowerRef`, emits a pair
of scratch writes at 0 and 32, then hashes 64 bytes to derive the record address.
Related address construction is in
[`StorageLayout.lean`](../Compiler/SolidityImport/StorageLayout.lean),
`computeSPathBaseSlot`. The key's assembly accesses are recorded separately by
[`BoundedMemory.lean`](../Compiler/SolidityImport/BoundedMemory.lean).

[`MemoryBounds.lean`](../Compiler/SolidityImport/MemoryBounds.lean), `store`,
currently accepts recorded source writes and the initial free-pointer prologue.
It rejects these generated scratch writes as synthetic memory effects. The
combined control reaches that guard after the full cleanup succeeds.

There is another boundary visible in the code: `scalar` excludes storage-read
expressions such as `storageArrayElement`. This is a prospective next rejection,
not an observed successful composition or a reason to remove the scalar check.
Accepting the scratch writes alone would not establish that the whole root is
supported. Event argument lowering and tail-only cleanup are separate follow-ups.

## Proposed minimal admission slice after #39

Keep the initial slice straight-line, fully cleaned and read-only. Analyze the
lowered statement sequence structurally, including helper-inlined operations.
Reuse or extend the existing effect summaries rather than introducing a global
"storage plus memory is safe" flag or a helper-name exception.

1. Recognize the mapping-address operation as a bounded, ordered scratch effect:
   two clean word writes in `[0,64)` followed by the corresponding hash. Preserve
   the original key and mapping-base expressions and their evaluation order.
   Do not classify arbitrary writes to these addresses as verified mapping work.
2. Compose that footprint with the existing source-access bounds: the packed
   buffer starts at or above 128, all writes including cleanup are nonwrapping,
   and `base + 96 <= 2^32`. Scratch writes must preserve the free-pointer word
   `[64,96)`, the zero word `[96,128)`, and the bounded source buffer.
3. Admit only storage-read expressions whose effects are understood. A storage
   result is an unconstrained word for subsequent interval reasoning; it cannot
   silently become a bounded pointer. Keep guard/version invalidation and reject
   unsupported control flow, external calls, writes and unresolved aliases.
4. Preserve restrictions on observations of synthetic layouts. The ABI-allocation
   and raw-scratch controls must remain rejected. No proof may assume that source
   Solidity exposes the importer's particular scratch or ABI allocation layout.

The mapping-slot preimage remains the independent `word32(key) ++ word32(base)`
expectation. Layout resolution and field extraction must remain construct-generic;
fixture slot numbers and identifiers must never enter production admission logic.

## Proof-only composition foundation

`Verity/Core/Model/MemoryComposition.lean` composes the existing physical word
writer into an ordered adjacent pair. Its generic byte-slice and coherent-word
frames preserve disjoint observations; its complete non-memory frame preserves
storage, events and the other world components while allowing memory expansion.

`Compiler/Proofs/IRGeneration/ScratchMemoryComposition.lean` identifies that pair's
64 bytes with the existing `abiEncodeMappingSlot` encoder in key-then-base order.
Under explicit nonwrapping bounds, the actual proof-IR memory reader and hash
consume this preimage. Scratch writes at 0 and 32 preserve the free-pointer and
zero words under initial coherence, and preserve arbitrary buffers above 128.
The disjoint-slice hash frame also handles unaligned buffers.

This is a foundation for the proposed admission slice. It does not recognize
lowered mapping operations, connect arbitrary source execution to the pair,
justify tail-only cleanup, or supply a storage-reference correspondence theorem.
The combined-root rejection remains required until the admission implementation
is separately accepted after #39 merges. All independent expectations are unchanged.

## Proof obligations and acceptance

Existing reusable results include `memory_writes_coherent`,
`memory_writes_byte_frame` and `memory_writes_frame` in
[`MemorySlice.lean`](../Verity/Core/Model/MemorySlice.lean), and
`ir_memory_slice_bytes_eq_physical` in
[`MemorySliceBridge.lean`](../Compiler/Proofs/IRGeneration/MemorySliceBridge.lean).
They provide ingredients, not a theorem proving this importer extension.

The implementation must establish the scratch/buffer disjointness and allocator
frame under explicit bounds, preserve the saved hash across mapping derivation,
and preserve persistent storage and logs for the read-only root. Use existing
state/frame lenses and small generic helper lemmas; retain current hash premises.
Audit and fast-check candidate statements before proving them with Turbo-Lean.
Any later Yul/ECM rewrite requires the repository's certified-shim framework;
this preparation proposes no instruction rewrite and adds no proof or axiom.

Acceptance for the implementation PR requires all three combined variants to run
through the actual Denote and generated-EVM sequence routes against the same
independent observations. Keep both source mutants detectable and all six excluded
boundary controls rejected. Only then replace the combined-root rejection checks
with mandatory three-route execution and allow the composition gate to pass.
A supplied-key control or successful import alone can never satisfy that gate.
Run exact-head repository, warning, proof, differential and mutation gates.

Tail-only cleanup needs a separate caller liveness/frame argument, prepared in
[the caller-liveness design](TAIL_CLEANUP_LIVENESS.md). Writes,
events, rollback and the always-reverting value-return root remain later work,
followed by validation of the pinned downstream wrapper tracked in #32. Full
cleanup does not substitute for any of those acceptance criteria.

## Running the preparation

```bash
PYTHONPATH=scripts python3 -m solidity_differential.check_packed_storage_read \
  --output .lake/packed-storage-read
```

`--prepared` reuses built importer, differential and sequence-runner interfaces.
Default exit 0 means only that the preparation matrix passed. Add
`--require-composition` for exit 1 after a successful preparation while the
combined Denote/generated routes remain absent. Unexpected admission, changed
rejection reasons, bad observations or tool failures produce exit 2. CI archives
the evidence with the other bounded-memory campaigns.
