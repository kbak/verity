# Full-cleanup rollback preparation

This prepares the next part of fork #32 on #62. It changes no importer admission,
compiler behavior, proof, fixture or independent expectation. Implementation must
wait for #62 to merge. Full-cleanup rollback remains unaccepted until actual source
EVM, imported Denote and generated Cancun EVM execute the complete frozen sequence.

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
The existing separate storage-control gate retains actual three-route rollback
coverage. It does not establish packed-hash/rollback composition.

## Two independently observed blockers

| Case | Importer | Compiler |
| --- | --- | --- |
| Full-cleanup packed root, with or without declared return values | Rejected by the memory-independent successful suffix audit | Not reached |
| Supplied-key root, no declared return values | Admitted | Compiles |
| Same supplied-key root, with declared scalar return values | Admitted | Rejected by exhaustive return-path validation |

The importer already marks a Solidity `RevertStatement` as terminal in
[`lowerRootStatements`](../Compiler/SolidityImport/Import.lean), but `lowerRevert`
represents the custom error as `Stmt.requireError (Expr.literal 0)`. The imported
control model retains that representation. The second blocker is the compiler's
[`stmtListAlwaysReturnsOrReverts` check](../Compiler/CompilationModel/Validation.lean),
which delegates to the structural control-flow summary in
[`Types.lean`](../Verity/Core/Model/Types.lean). That summary conservatively permits
fallthrough for every `requireError`, including a literal-zero condition;
`revertError` itself is already classified as terminal. The regression invokes
the actual compiler and requires its exact structured rejection. Evaluation
errors cannot satisfy this check. No source return declaration is removed to
claim acceptance of the original packed root.

## Implementation stages after #62 merges

1. **Literal-zero custom-error guard classification.** Refine the canonical
   structural summary for `requireError (literal 0)` to record no successful
   fallthrough. Preserve the imported representation and the final return-path
   check. True and unknown conditions must still permit fallthrough; reject raw
   `stop` for declared returns and reject a conditional with a falling-through
   alternative. Check direct metadata and recursive summary consistency, argument
   evaluation failures and sequential composition. Do not add dummy returns or
   infer terminality from a function name. The supplied-key declared-return
   control must then compile and match all three routes on the unchanged sequence.
2. **Bounded terminal custom errors after storage effects.** Extend the structural
   suffix audit only for terminal custom errors, including the current literal-zero
   `requireError` representation, with supported static scalar
   parameters and memory-independent arguments. Retain all existing guards
   against subsequent memory observations, calls, loops and unsupported branches.
   Preserve the existing lowering order and complete mapping-scratch provenance.
   The original full-cleanup root must execute the entire frozen sequence through
   all three routes; both blocker regressions must become positive execution gates.

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
