# Full-cleanup rollback boundary and terminal error guards

This tracks the next part of fork #32 after #62 and #63. Literal-zero custom-error
guards now have terminal control-flow metadata, allowing the supplied-key root
with declared return values to compile and execute on all three routes. Packed
rollback admission remains unchanged: the full-cleanup root still rejects until
the bounded post-effect revert audit is implemented. Fixtures and independent
expectations remain unchanged.

## Regression contract

The campaign uses the existing full-cleanup source variant of
`PackedStorageReference.sol`. It retains the complete independent state archives
for both mapping layouts and the packed-byte/hash archive. No transactions or
expected observations are removed or regenerated from an imported model.

The sequence covers successful updates interleaved across keys, writes followed
by custom-error reverts on existing and empty records, and subsequent reads.
Each revert must preserve the previous persistent state, discard its logs and
produce the exact `Rejected(uint128)` selector and argument bytes. Comparisons
include every record field, high padding, other keys and surrounding sentinel
slots, using the existing cumulative discovery/replay protocol.

Original, renamed-helper, shifted-layout and void-return full-cleanup variants
run on the actual source EVM. Removing the revert must expose state and log
changes as well as incorrect status/data and later read results. Changing the
error argument, selector or replacing it with an empty revert must change only
the reverted transactions' payloads. Missing observations, infrastructure failures
and unexpected mismatches fail preparation. Unit tests separately corrupt
observations to check state/log-leak sensitivity; these are comparator tests,
not execution evidence for a broken backend.

The supplied-key control also runs its complete source sequence, with and without
declared return values on its always-reverting root. Only control inputs use
precomputed keys; expected observations and transaction environments stay intact.
The declared-return control now also runs the complete unchanged sequence through
actual Denote and generated Cancun EVM. A changed error argument must affect only
the exact reverted payloads on every route, preserving state, logs and successful
calls. The existing separate storage-control gate remains required. Neither
supplied-key control establishes packed-hash/rollback composition.

## Current admission and compilation boundaries

| Case | Importer | Compiler |
| --- | --- | --- |
| Full-cleanup packed root, with or without declared return values | Rejected by the memory-independent successful suffix audit | Not reached |
| Supplied-key root, no declared return values | Admitted | Compiles |
| Same supplied-key root, with declared scalar return values | Admitted | Compiles and agrees on all three routes |

The importer already marks a Solidity `RevertStatement` as terminal in
[`lowerRootStatements`](../Compiler/SolidityImport/Import.lean), but `lowerRevert`
represents the custom error as `Stmt.requireError (Expr.literal 0)`. The imported
control model retains that representation. The compiler's
[`stmtListAlwaysReturnsOrReverts` check](../Compiler/CompilationModel/Validation.lean),
which delegates to the structural control-flow summary in
[`Types.lean`](../Verity/Core/Model/Types.lean), previously allowed fallthrough for
that representation. Direct metadata and the recursive summary now classify
only the syntactic `requireError (literal 0)` case as terminal. Other conditions
retain their conservative classification. The final return-path check, imported
statements, argument lists and generated lowering are unchanged.

The regression invokes the actual compiler on the imported root and controlled
tail variants. True and unknown guards, a falling-through conditional alternative
and raw `stop` must retain the exact return-path rejection. A zero guard followed
by unreachable `stop`, and a conditional whose alternatives both revert, compile.
Evaluation failures cannot satisfy any compiler result check.

[`DenoteErrorGuard.lean`](../Verity/Core/Model/DenoteErrorGuard.lean) proves that
direct and recursive metadata agree, every guard argument remains visible to
other audits, and the zero guard returns the existing custom-error bytes or
reverts when argument evaluation/encoding fails. It cannot continue, return or
execute a later statement. These are local Denote/control-flow lemmas, not a
global soundness proof for the complete control-flow analysis or importer.

## Completed slice and next implementation stage

1. **Literal-zero custom-error guard classification: implemented.** The generic
   structural refinement and local proofs preserve the imported representation,
   final return-path check and all independent expectations. The supplied-key
   declared-return control now requires real three-route agreement and error-byte
   mutation sensitivity; no dummy returns or function-name dispatch are added.
2. **Bounded terminal custom errors after storage effects.** Extend the structural
   suffix audit only for terminal custom errors, including the current literal-zero
   `requireError` representation, with supported static scalar
   parameters and memory-independent arguments. Retain all existing guards
   against subsequent memory observations, calls, loops and unsupported branches.
   Preserve the existing lowering order and complete mapping-scratch provenance.
   The original full-cleanup root must execute the entire frozen sequence through
   all three routes. Promote the packed rejection controls to positive execution
   gates while preserving the full frozen expectations and negative boundaries.

The second stage must account for the actual
[`revertWithCustomError`](../Compiler/CompilationModel/AbiEncoding.lean) encoder:
it stores and hashes the error signature at the free pointer, then writes the
selector and encoded arguments at low memory before reverting. Bound the rounded
signature writes at the tracked free pointer and the complete scalar payload
footprint, including full-word stores. For `n` one-word scalar arguments, the low
write footprint ends at `max(32, 4 + 32*n)`; returned error data has length
`4 + 32*n`. Establish nonwrapping bounds and exclude dynamic/aggregate encoding
from this first slice. Error arguments may use captured scalars and raw storage
reads, but must not observe scratch memory overwritten by the encoder.

Terminality makes scratch preservation after the revert unnecessary; it does not
permit bypassing bounds, dropping error bytes or committing state/log changes.
[`Denote`](../Verity/Core/Model/Denote.lean) produces custom-error data, while
[`SequenceRunner`](../Compiler/SolidityImport/SequenceRunner.lean) compares traced
results against public Denote and settles the transaction. Keep those existing
rollback boundaries intact. Retain cumulative slots touched by reverted calls in
the shared replay plan, including independently selected sentinels.

Acceptance requires rollback-sensitive execution mutants on each implemented
route, exact errors and continued post-revert state checks. Source mutants alone
are preparation evidence. Existing read/update, tail-cleanup rejection and
supplied-key control gates must remain green, together with exact-head repository
verification. Do not claim that finite execution proves importer/compiler
correspondence, general frame equivalence, gas/resource adequacy or constructors.
Existing memory/frame hypotheses and hash/environment premises remain unchanged.
Tail-only cleanup and the pinned downstream wrapper remain separate #32 work.

## Running preparation

```bash
PYTHONPATH=scripts python3 -m solidity_differential.check_packed_storage_rollback \
  --output .lake/packed-storage-rollback
```

`--prepared` reuses built interfaces. `--require-composition` deliberately fails
after successful preparation: packed Denote/generated-EVM execution is still
missing. Preparation never reports three-route packed rollback agreement.
