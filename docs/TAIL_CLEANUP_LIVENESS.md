# Tail-only cleanup and caller liveness

This is regression and design preparation for #32, stacked on fork PR #49.
Importer admission remains unchanged. Wait for #39 to merge before implementing
any admission extension; the full-cleanup read composition in
[the preceding design](PACKED_STORAGE_READ_DESIGN.md) remains the earlier slice.

## What remains observable

The unchanged packed helper hashes `[base + 12, base + 70)` and then clears
`[base + 64, base + 96)`. The hash is saved before cleanup. The unknown upper
96 bits of the address word can remain in `[base, base + 12)`. Other residual
nonzero payload bytes are not automatically dirty: liveness must track unknown
bits separately from known data. Rehashing the buffer after cleanup is not an
acceptable replacement for preserving the saved digest.

The current bounded-memory analysis rejects remaining dirty scalar bytes at
assembly exit, before a caller can establish their irrelevance. That boundary
stays mandatory in this PR. A memory-safe annotation alone supplies no proof that
a caller cannot observe the residual bytes.

## Executable preparation

`TailCleanupCaller.sol` is a separate, unannotated assembly probe. It injects
0, 1, or the maximum 96-bit value into the address word's upper bits. These bits
are outside the frozen 58-byte preimage. The probe uses all seven existing
aligned/unaligned base shifts and all 54 existing packed vectors. Original packed
and storage fixtures, expected hashes, and both state archives are unchanged.

Only caller continuations vary. Every run still compares its return against the
original packed digest; unsafe continuations must produce an exact inventory of
mismatches, not new expected digests or ignored failures.

| Caller | Required source observation |
| --- | --- |
| Return saved hash | Original hash for every poison. |
| Overwrite the prefix before reading | Original hash for every poison. |
| Read the disjoint, cleared tail word | Original hash for every poison. |
| Overwrite through an alias equal to the base | Original hash for every poison. |
| Read prefix, then overwrite it | Nonzero poison must change the return. |
| Overwrite starting twelve bytes too late | Nonzero poison must change the return. |
| Read the byte at offset 11 through an unaligned word | Nonzero tested poison must change the return. |
| Overwrite through a parameterized alias | Offset 0 hides poison; offset 32 exposes nonzero poison. |

The 10,206 calls are finite source-EVM evidence under the pinned Solidity 0.8.26,
Cancun, via-IR and optimizer settings. There are 3,024 required mismatches. Missing
observations, reverts, wrong return widths, unexpected mismatches and missing
sensitivity all fail the campaign. Eight probe imports and all five unchanged
storage-reference roots must retain the located dirty-byte rejection.

The harness archives source variants, inputs, real observations, runtimes,
compiler/node identities, implementation identities and the frozen expectation
checksums. Full state archives are preserved as provenance; this stateless campaign
does not replay their transactions. The existing storage sequence campaigns still
own those obligations. Denote/generated-EVM execution of these tail-only roots
is explicitly missing; separate full-cleanup controls cannot fill that gap.

## Proposed caller contract

A future generic analysis should express a relation between executions whose
memory agrees outside a residual unknown-bit mask, with equal live scalar results
and the required world/allocator frame. It must establish that each observable
continuation preserves agreement. A finite poison test cannot prove this relation.

Start with straight-line, bounded, nonwrapping operations and known aliases:

1. Carry residual masks across the helper boundary only inside an analyzed
   continuation. The call boundary does not erase the mask. A standalone root
   that exports an unresolved obligation remains rejected.
2. A write kills only the bits it actually overwrites, and only after its address
   and value dependencies have been checked. A dominating full prefix overwrite
   can discharge a subsequent read; a tail write cannot. Reads before writes may
   propagate dirty bits into live scalar values even if memory is later cleaned.
3. Prove read footprints disjoint from live dirty bits, or propagate those bits
   into scalar dependency masks until a proven mask operation removes them.
   Treat `mload` as a 32-byte read, including unaligned overlap; `keccak256` reads
   its exact interval. Conservatively reject unsupported scalar propagation.
4. Establish aliases from structural bounds/equalities and guarded values, with
   invalidation after assignments. A parameter constrained to `[0,32]` does not
   establish that the cleanup address equals the base. Unknown aliases reject.
5. Include return/revert/log byte ranges, call input, memory copies, allocations
   and later helper effects in the observation model. External calls, loops,
   branches, dynamic copies and unresolved allocation lifetimes are outside the
   first slice. Reject them until their effect/merge rules are established.

Returning a saved clean hash is safe in the source experiment because the tested
continuation never exposes the prefix. A proof must also account for ABI return
construction and reuse of the free-pointer buffer. Preserve the free-pointer and
zero words, live buffers, storage, logs and required world components explicitly.
Memory expansion and gas are separate observations: these experiments do not
establish gas equivalence or equality of memory size. No arbitrary initial-memory
or allocator assumption may be inferred from successful deployment tests.

Use #49's disjoint byte-slice, coherent-word and non-memory frames as ingredients
where their hypotheses hold. They do not prove this relational caller contract,
source/importer equivalence, or permission to admit arbitrary scratch reads.
Keep all production logic construct-generic and independent of fixture names.

## Subsequent implementation acceptance

After #39 and the preceding full-cleanup slice merge, first prove the minimal
straight-line caller relation and integrate it with structural effect analysis.
Use small kernel-checked lemmas, explicit address bounds, the existing hash
premises, and existing state lenses; add no axiom or proof shortcut.

A separate implementation PR must replace appropriate positive rejection checks
with actual imported Denote and generated Cancun execution against the same
frozen hashes. Unsafe callers, unresolved aliases and unsupported observations
must retain explicit rejections. Do not turn failed perturbations into passing
expectations. The original tail-only storage helper must then pass its unchanged
29-transaction state sequence on all three routes, including adjacent slots,
other keys, events and rollback. That broader storage support and the pinned
downstream wrapper remain later #32 acceptance work, not claims of this PR.

## Running and interpreting the gate

```bash
PYTHONPATH=scripts python3 -m solidity_differential.check_tail_cleanup_liveness \
  --output .lake/tail-cleanup
```

`--prepared` reuses the importer build. Default exit 0 certifies preparation only.
`--require-composition` exits 1 after successful preparation because the tail-only
model/generated routes remain absent. Unexpected admission or rejection changes,
invalid observations, and infrastructure failures exit 2. CI retains the evidence
with the other bounded-memory campaigns.
