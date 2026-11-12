# Full-cleanup packed hash and storage read

This implements the read-only full-cleanup composition slice of #32 after #39
merged. Tail-only cleanup, writes, events, rollback and the pinned downstream
wrapper remain separate work; this slice does not complete #32.

## Executable boundary

`Contracts/SolidityImportSmoke/PackedStorageRead.sol` separates three roots:

| Root or variant | Required execution evidence |
| --- | --- |
| `digest` with full cleanup | All 54 existing packed vectors agree across source EVM, actual Denote and generated Cancun EVM. |
| `readKey` with a supplied key | Six initial reads agree across those same three routes. |
| Combined `read`, helper rename, shifted layout | The unchanged initial reads match the independent oracle across source EVM, actual Denote and generated Cancun EVM. |
| Caller reads the cleared buffer after lookup | All three routes preserve the same independent reads; the source checks that all cleanup words remain zero. |
| Wrong mapping base, shortened hash | All three real execution routes must disagree with the oracle only in return data, and agree with each other; failures or state corruption do not count as detection. |
| Partial cleanup, dirty hash, dirty word read, unknown cleanup alias | Source-valid roots retain their respective located rejections. |
| ABI allocation before the hash | Retains the synthetic-memory-write rejection. |
| Raw scratch read after lookup | Retains the existing `unsupported Yul builtin mload` rejection. |
| Storage write, storage-derived pointer or free pointer, source-written scratch pair | Retain their respective root-audit rejections. |

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
reported separately from the required combined execution.

Source reads use the existing cumulative discovery/replay slot plan. Unexpected
slots must retain their initial values; missing observations or tool failures
cannot pass. Model controls use the actual imported model and generated Yul;
implementation identities, compiler/settings, deployments and observations are
retained. Pure hash controls execute with empty initial storage; stateful read
controls install the independently specified initial storage. These are finite
experiments, not constructor, balance/nonce, gas or whole-world equivalence.

## Admission and effect boundary

[`StorageLayout.lean`](../Compiler/SolidityImport/StorageLayout.lean),
`mappingScratch`, emits the existing ordered writes at 0 and 32 followed by the
64-byte hash. It allocates a hygienic fresh result and records that binding as
lowering provenance. Struct mapping address construction shares this emitter;
the emitted operands, binding allocation order and model statements are unchanged.
Provenance is reset for each imported root and never inferred from source names.
The emitter source is included in the importer digest. A source-written scratch
pair with a compiler-style local name remains an explicit rejection control.

[`MemoryBounds.lean`](../Compiler/SolidityImport/MemoryBounds.lean) scans the
lowered root in source order. It consumes only an adjacent, intact mapping
sequence with a recorded fresh result, removing that result from the provenance
set. Arbitrary source-written scratch pairs, reordered or interrupted sequences,
and synthetic ABI allocation writes still reject. Each operand must also pass
the existing scalar-expression effect audit. This is a linear scan with hash-set
provenance, not a global permission to combine storage and memory.

The scratch footprint `[0,64)` is disjoint from the allocator word `[64,96)`,
the zero word `[96,128)`, and source buffers at or above 128. Recorded source
accesses still require nonwrapping bounds, including the full cleanup footprint.
The scratch operation therefore retains the preceding free-pointer range and
scalar bindings; only its fresh hash result is bound. No generated instruction is
rewritten or reordered and no source memory layout is assumed observable.

Scalar storage-array reads are admitted in this straight-line root. Their values
remain unknown words in the interval analysis, as do hash results. Reading storage
does not establish a pointer bound. Existing successful guards and binding-version
invalidation still apply; writes, external calls, loops and unsupported branches
remain excluded. Dirty-bit cleanup requirements in `BoundedMemory.lean` are
unchanged, so tail-only cleanup still rejects before this composition audit.

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

These existing lemmas justify the physical scratch footprint and its frames.
The new recognition and interval checks remain trusted frontend code; the lemmas
do not connect arbitrary Solidity execution to an accepted root, justify tail-only
cleanup, or supply a storage-reference correspondence theorem. No new proof or
cryptographic assumption is introduced. All independent expectations are unchanged.

## Proof obligations and acceptance

Existing reusable results include `memory_writes_coherent`,
`memory_writes_byte_frame` and `memory_writes_frame` in
[`MemorySlice.lean`](../Verity/Core/Model/MemorySlice.lean), and
`ir_memory_slice_bytes_eq_physical` in
[`MemorySliceBridge.lean`](../Compiler/Proofs/IRGeneration/MemorySliceBridge.lean).
They provide ingredients, not a theorem proving this importer extension.

The physical frame lemmas preserve allocator metadata and source buffers under
their explicit coherence/disjointness bounds, as well as persistent storage and
logs. The admission change preserves the existing generated instruction sequence
and uses fresh names to preserve previously computed hashes. It does not discharge
the remaining source/importer or compiler correspondence obligations. Any later
Yul/ECM rewrite still requires the repository's certified-shim framework.

Acceptance requires all combined variants to run through the actual Denote and
generated-EVM sequence routes against the unchanged independent observations.
Both source mutants must remain detectable on every route and all excluded
boundary controls must reject. Separate hash/key controls or successful import
alone cannot pass the composition gate. Repository, warning, proof, differential
and mutation checks remain required on the exact PR head.

Tail-only cleanup needs a separate caller liveness/frame argument. Writes,
events, rollback and the always-reverting value-return root remain later work,
followed by validation of the pinned downstream wrapper tracked in #32. Full
cleanup does not substitute for any of those acceptance criteria.

## Running the regression

```bash
PYTHONPATH=scripts python3 -m solidity_differential.check_packed_storage_read \
  --output .lake/packed-storage-read
```

`--prepared` reuses built importer, differential and sequence-runner interfaces.
Exit 0 requires combined execution, independent observations, mutation sensitivity
and all rejection controls to pass. `--require-composition` remains accepted for
existing callers, but composition is now mandatory with or without the flag.
Missing routes, changed rejection reasons, bad observations or tool failures fail
the campaign. CI archives the evidence with the other bounded-memory campaigns.
