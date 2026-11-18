# Tail-only cleanup and caller liveness

The importer admits an inlined helper with tail-only cleanup when the caller
returns the saved hash. Earlier fork work covers bounded-memory
lowering and full-cleanup storage reads. [PR #39](https://github.com/kbak/verity/pull/39)
and [PR #56](https://github.com/kbak/verity/pull/56).

## What remains observable

The unchanged packed helper hashes `[base + 12, base + 70)` and then clears
`[base + 64, base + 96)`. The hash is saved before cleanup. The unknown upper
96 bits of the address word can remain in `[base, base + 12)`. Other residual
nonzero payload bytes are not automatically dirty: liveness must track unknown
bits separately from known data. Rehashing the buffer after cleanup is not an
acceptable replacement for preserving the saved digest.

The assembly-level dirty-byte masks must show that the hash reads clean bytes.
If residual bytes remain, an inlined helper may defer its exit check to the root
when it assigns that hash to its result and ends with a store. The root matches
the fresh hash and final store bindings, checks each zeroing store's heap bounds,
and follows copies of the result through the caller. Reassigning a binding drops
its previous value. The caller may read allocator word `0x40` and restore it to
the entry value `0x80`. With that pointer restored, the caller can return the saved word directly
or use it as the key for a read-only record lookup. Writes carrying dirty scalar bits must stay in
the heap. A memory-safe annotation grants no additional access.

## Executable coverage

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
sensitivity all fail the campaign. The saved-hash probe must also match every independent return in imported Denote
and generated Cancun bytecode. The seven other continuations and the four write or rollback
roots must produce located rejections. The original storage-reference read must
match the archived observations on all three routes. Separate import controls
exercise a reassigned result, a missing restore and a different final pointer.

The harness archives source variants, inputs, real observations, runtimes,
compiler/node identities, implementation identities and the frozen expectation
checksums. The storage campaigns replay the state archives. The tail-only read also checks every accessed physical slot against the
independent mapping address, including reads of empty records.

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

## Proof-only caller observations

`Verity/Core/Model/MemoryObservation.lean` proves a two-run overwrite law using
pointwise physical-byte equality, compatible with the existing `OwnedEq` memory
frames. For a common list of word writes, a queried byte needs initial agreement
only if every write misses it. The exact slice and coherent word-read lemmas lift
that law to arbitrary, including unaligned, observation windows.

The residual-set form assumes the initial memories agree outside an explicit
set of byte addresses. Every residual byte within the later read range must be
covered by a write. It does not require cleanup of bytes that remain unobserved.
The set is a conservative byte-level parameter, not an implemented dirty-bit
analysis. Equal byte observations do not require equal allocated memory sizes.

`Compiler/Proofs/IRGeneration/CallerMemoryComposition.lean` transports the byte
agreement through the existing proof-IR slice reader and concrete memory hash.
Both coherent word views and the reader's rounded, nonwrapping address bound
are explicit hypotheses. Equal hash inputs give equal outputs without a new
hash axiom or a change to the existing hash faithfulness/collision premises.

These theorems require the same **evaluated addresses and values, in the same
order**, in both executions, followed by the observation. Syntactically identical
caller code does not establish that premise. They do not erase a previously
captured scalar, infer an alias, prove a caller's residual set, compare memory
sizes/gas, or establish equality of other world fields. Existing non-memory and
allocator frames remain separate obligations. Core addresses are natural numbers;
consumers connecting writes to modular EVM addresses must establish their bounds.

This supplies proof ingredients for the earlier design. A complete caller effect
analysis, ABI-return/allocator reasoning and source/importer correspondence are
still pending.

## Bounded literal execution bridge

`BoundedMstoreExecution.lean` connects a straight-line list of literal `mstore`
statements to the canonical source interpreter, `execStmtsCanonical`. Execution
continues with exactly the ordered physical-write fold used above. Every write
must fit its entire 32-byte footprint below the EVM address modulus, and word
values are typed `Uint256` literals. These conditions make the evaluated operands
identical in both runs without assuming equality of their initial memories or
bindings. Empty lists, overlapping writes and unaligned addresses are included.

The exact poststate also gives a complete runtime frame: after erasing both
memory views, the initial and final runtime states are equal. This preserves
bindings, immutable values, external-call bookkeeping and all non-memory world
fields, including storage and events. It permits memory expansion and does not
claim that two different initial states have equal non-memory fields.

`BoundedMstoreObservation.lean` then compares actual canonical `mload` and
`keccak256` expression results after successful executions of that block. Initial
physical bytes must agree within the observation range wherever every write
misses. Both initial word views must be coherent. Literal offset and size bounds
prevent modular truncation, and the existing rounded nonwrapping hash-reader
bound remains explicit. The load observes all 32 bytes; the hash observes its
exact selected slice. No hash premise is added or weakened.

This bridge proves source execution and observations for literal blocks. It does
not derive equal operands for arbitrary expressions, infer aliases or residual
masks, erase earlier captured scalar values, prove ABI return/allocator behavior,
or establish source/compiler correspondence or generated-EVM equivalence. The
existing rejection gates and independent expectations remain unchanged.

## Parameter and local-variable store bridge

`BindingMstoreOperands.lean` describes bounded literals, present parameter/local
bindings and nonwrapping constant additions. Its witnesses establish evaluation
by the canonical interpreter independently of memory. Binding agreement compares
only the names used by those operands, including binding presence; unrelated
bindings may differ. Each referenced scalar must already fit a full EVM word.

`BindingMstoreExecution.lean` composes these witnesses into store-only blocks with
explicit nonwrapping 32-byte footprints. Agreement on the referenced bindings
derives the same resolved write list in the second runtime. The block executes
to exactly the literal-store result from the preceding bridge, including the
complete non-memory runtime frame. No assignment or memory-dependent operand
can be represented by this witness. Missing bindings cannot use the interpreter's
default zero, and overflowing constant additions have no witness.

`BindingMstoreObservation.lean` reuses the preceding load/hash theorems after
actual block execution. Coherence, byte agreement outside the writes, and all
observation bounds remain explicit. These results cover pointer-plus-constant
addresses and scalar values without equating unrelated runtime fields.

Binding agreement is a hypothesis, not an inferred provenance or liveness fact.
A value captured from dirty memory before cleanup is not made equal by later
stores. This slice does not analyze aliases, assignments, branches or calls,
prove ABI return/allocator behavior, or establish compiler/generated-EVM
correspondence or gas/memory-size equality. It adds no importer admission rule;
all independent expectations and rejection gates remain unchanged.

## Returning a saved hash after cleanup

`SavedHashReturn.lean` proves the canonical execution of a hash assignment,
a store-only cleanup block, and a return of the saved local. The initial word
and byte views must agree, and the rounded word window used to read the hash
must fit in the address space. The digest covers exactly the requested bytes.
Each cleanup store has a resolved address, value, and nonwrapping footprint.
The proof identifies the exact poststate after those writes, including the
original digest in the return words.

Two executions with the same physical preimage therefore return the same word.
Their bytes outside the preimage may differ, and their cleanup stores may
overwrite part or all of the preimage after capture. For the source probe, the
tail store overwrites the final six bytes of the 58-byte input after hashing.
The proof takes the preimage at capture as a premise. Establishing it from the
preceding packing stores belongs to the caller analysis.

For an external return of a single local, the compiler emits `mstore(0, local)`
and `return(0, 32)`. Given the saved word in that IR local, the IR interpreter
returns it and writes its big-endian bytes at offsets 0 through 31. The importer checks the
copy chain through the inlined caller and the final free-memory pointer. The
three-route campaign exercises that connection for the pinned compiler profile.

## Subsequent implementation acceptance

The importer follows copies of the saved hash into the key word of a generated
mapping preimage. It checks the fresh slot binding, the exact layout base and
the restored allocator before accepting the hash of scratch bytes 0 through 63.
The suffix may read the resulting raw storage slot and fields at literal word
offsets, apply a literal field mask and return those words. Its static return
buffer must fit below byte 128. A substituted key, a memory observation, a write
or a revert in this suffix still rejects.

The original read runs on source Solidity, imported Denote and generated Cancun
bytecode using the frozen initial reads. Each route must touch the exact three
record slots for each key, return the expected bytes and preserve storage and
logs. A shifted-layout control and a wrong-base control exercise slot selection.

The original tail-only storage helper must then pass its unchanged
29-transaction state sequence on all three routes, including adjacent slots,
other keys, events and rollback. That broader storage support and the pinned
downstream wrapper remain later #32 acceptance work, not claims of this PR.

## Running and interpreting the gate

```bash
PYTHONPATH=scripts python3 -m solidity_differential.check_tail_cleanup_liveness \
  --output .lake/tail-cleanup
```

`--prepared` reuses the importer and differential runner. The default gate
requires the saved-hash caller to pass all three routes, the source perturbations
to expose the expected bytes, and unsupported callers to produce located
rejections. `--require-composition` also requires the broader tail-only work,
including writes and rollback, and still reports it as pending.
