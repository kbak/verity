# Full-cleanup successful storage updates and logs

This extends #32's full-cleanup read composition to successful raw storage-word
updates and scalar events. It does not complete #32: write-then-revert composition,
tail-only cleanup and the pinned downstream wrapper remain separate work.

## Admission boundary

The root audit first checks the existing bounded source-memory operations and
complete generated mapping-scratch sequences. The first raw storage-word write
or scalar event switches structurally to a restricted suffix. That suffix accepts
word bindings, raw storage reads/writes, scalar events and scalar return/stop.
Its expressions cannot read or hash memory or use synthetic storage layouts.
Calls, guards, branches, loops, allocations and explicit reverts are rejected.
There is no path back to the source-memory phase, including through another
lookup helper. No global effect flag or function-name allowlist is used.

Raw writes retain the existing lowering: full words use the raw storage channel;
narrow fields preserve the other bits through the existing read/mask/write
sequence. The generated instructions and their order do not change. A stored
value remains an unknown word for pointer analysis; it supplies no new bound.

Events must satisfy the compiler's scalar-event predicate. Both the rounded
signature-buffer footprint and unindexed data words must fit below the existing
memory bound at the current free pointer. The pointer must remain above the
allocator and zero words. This matters because generated scalar events write
their signature and payload into memory. Source and generated event encodings
need not leave identical scratch bytes. Later memory loads, hashes and lookups
therefore remain rejected. Earlier captured clean scalars remain available.

An explicit revert after a write or log remains outside this suffix, even though
the existing supplied-key control exercises rollback independently. Guard failures
before these effects retain their existing treatment. The restriction does not
claim gas or resource adequacy, or successful execution for arbitrary inputs.

## Independent execution gate

The campaign reuses the existing full-cleanup variant of
`PackedStorageReference.sol`; the original tail-only fixture is unchanged. It
retains both complete state archives and all packed expectations, checking the
existing frozen hashes before selecting the contiguous successful prefix ending
immediately before the first write-then-revert transaction. Expected return bytes,
logs, persistent state, transaction identities and initial storage are copied
unchanged. The prefix covers seeded and empty records, each field, repeated
narrow-field updates, interleaved keys, high padding and surrounding sentinels.

Source EVM, actual imported Denote and generated Cancun EVM execute this prefix
for the original full-cleanup control, renamed helpers and shifted layout. The
shared discovery/replay protocol observes the cumulative union of every route's
touched slots plus independently selected sentinels. Every step must match the
independent oracle; agreement between routes alone is insufficient.

Wrong mapping bases, wrong fields and omitted source events must be detected on
all three routes without unexpected execution failures or inter-route divergence.
Separate Denote-only and generated-EVM-only event-deletion mutants must change
exactly the affected route's logs, preserving returns and state. Missing routes,
missing observations, changed archives and tool failures fail the campaign.

The read campaign retains its former unexpected-write source unchanged and now
executes it as a mutant: every route must detect both return-data and state
corruption against the original read expectations. A new memory-after-write
rejection replaces its obsolete admission boundary. The update campaign also
requires located rejections for memory reads/hashes and another lookup after
logging, guards after writes, logging before hashing, overflowing event footprints,
and explicit write-then-revert roots. Existing tail-only controls remain mandatory.

## Trust and remaining work

This is a trusted frontend admission extension with finite execution evidence.
It adds no theorem, axiom, cryptographic premise or instruction rewrite. Existing
physical memory/frame lemmas keep their explicit coherence and nonwrapping
hypotheses; they do not prove the importer recognizer or source/compiler
correspondence. Storage frames and exact logs are tested here, not established
for arbitrary Solidity executions. Constructor, gas, whole-world equivalence,
tail-only caller analysis and the complete rollback sequence are not claimed.

Run the mandatory regression with:

```bash
PYTHONPATH=scripts python3 -m solidity_differential.check_packed_storage_updates \
  --output .lake/packed-storage-updates
```

`--prepared` reuses built interfaces. Success requires all three real routes,
mutation sensitivity and the rejection boundary; source-only evidence cannot pass.
