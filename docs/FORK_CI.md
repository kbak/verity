# CI in the kbak/verity fork

The upstream workflows require a private self-hosted runner fleet. Only
`github.repository == 'kbak/verity'` selects the fork configuration:

- All `Verify proofs` jobs and the Turbo-Lean job use `ubuntu-24.04`.
- Lean uses two threads per process on hosted machines. Job timeouts and
  validation commands are unchanged; a resource failure must remain a failure.
- Host-local cache mounts, artifact publication, cleanup, and local restore
  attempts are skipped. Existing GitHub cache and artifact paths provide the
  cross-job transfer. Setup reclaims unused Android, .NET, and GHC SDK space
  only on the fork's disposable GitHub-hosted images.
- `checks` checks out the PR head SHA, runs `make check` on committed inputs,
  and neither regenerates nor auto-commits derived files. A stale fixture or
  report fails validation and must be regenerated in the development checkout.
- OCR is skipped: this fork has no model endpoint or credentials. This is
  absent review evidence, not a green semantic-review result. Human review
  remains necessary.

Other repositories retain the upstream runner labels and persistence behavior.
Keep this patch on the fork infrastructure branch; do not include it in an
upstream feature submission.

## Rollout

`pull_request` workflows use the PR merge ref. Each existing PR head must
contain this patch (merge the infrastructure branch through the stacked PRs).
Re-running an old run reuses its old workflow revision and cannot repair its
runner labels. Cancel obsolete queued runs after fresh runs have been created.

`pull_request_target` uses the PR base revision. Until the OCR guard reaches
all base branches, disable `ocr-review.yml` in this fork's Actions settings.
Do not enable it unless its endpoint and credentials have been deliberately
configured and the fork guard has been revised. No upstream setting changes
are needed.

## Evidence and limits

A started job establishes runner availability, not proof correctness. Check
`Verify proofs / ci-gate` and the individual build, audit, Foundry, and Turbo-Lean
results before claiming a PR is validated. Cold hosted builds have no upstream
warm caches; runtime, memory, and disk limits can still expose failures.
Mutation and extended regression campaigns retain their existing schedule,
manual-dispatch, and PR-label conditions (`ci:mutations`, `ci:full`).

Local configuration validation:

```sh
python3 scripts/generate_verify_sync_spec.py --check
python3 scripts/check_verify_sync.py
make check
actionlint -shellcheck= -pyflakes= -ignore 'label .* is unknown' \
  .github/workflows/verify.yml .github/workflows/turbo-lean-cache.yml \
  .github/workflows/ocr-review.yml
```

The actionlint label exclusion applies to the retained upstream custom labels;
runner routing itself is checked by the strict workflow spec and regression
tests. ShellCheck and Pyflakes are separate from this syntax/expression check.
