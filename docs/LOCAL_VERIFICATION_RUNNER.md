# Local verification runner

`scripts/run_verification.py` runs scoped checks with one shared admission budget
and a dedicated persistent Turbo-Lean worker owner. It requires Linux cgroup v2,
a working user systemd manager with delegated memory controls, Python 3.10+, and
the project's pinned Turbo-Lean and Lean toolchains. Standard CI commands remain
available; this runner replaces temporary local campaign wrappers.

## Prepare once per tested checkout

Keep the checkout itself outside `.lake`: repository scanners exclude generated
build trees. Generated Lean drivers, supplemental output and runner state belong
inside that checkout's `.lake` directory.

```bash
python3 scripts/run_verification.py init \
  --turbo /path/to/pinned/turbo-lean \
  --cgroup "$(systemctl --user show --property=ControlGroup --value -- -.slice)/verification.slice"
```

`init` copies the pinned executable into the runner's private tools directory and
creates tool adapters. The executable path distinguishes its persistent server
from other checkouts' servers. It starts no services. Existing configuration and
executables are never overwritten. Use a distinct slice for each independent
runner; do not run concurrent full campaigns on the same host.

Review the generated configuration before `start`. The example defaults are a
26 GiB soft cap, 28 GiB hard cap, 27 GiB admission budget, 4 GiB host reserve,
10 GiB shared-pool reservation and at most five 3.25 GiB mutation jobs. They are
starting values for a sufficiently large host, not portable performance promises.
Profiles, concurrency, pressure threshold and reserves are configurable. Every
profile must fit alongside the shared-pool reservation. The Foundry profile
reserves 6 GiB of host memory; it does not override Foundry's EVM memory setting.

```bash
python3 scripts/run_verification.py start
python3 scripts/run_verification.py run --kind mutation --name helper-copy \
  -- python3 scripts/solidity_import_mutations.py --task helper-copy-source --jobs 1
python3 scripts/run_verification.py run --kind foundry --name foundry-focused \
  -- forge test --match-test testDifferential_Random10000 --threads 2
python3 scripts/run_verification.py supplemental packed-storage-read
python3 scripts/run_verification.py stop
```

Use `--config` **before** the subcommand for a different configuration location.
Use the repository's prepared Python environment when a check needs its pinned
dependencies (`supplemental --python` selects that interpreter). Preparation is
explicit: use the exclusive `build` profile for required `turbo-lean build`
commands before launching checks that use `--prepared`.

## Guarantees and boundaries

- Each invocation gets a fresh request, log and status directory. Failed launches
  and failed tests remain available; reruns never overwrite them. Exit failures
  propagate to the caller. A timeout or readiness failure cannot count as a pass.
- The daemon and launchers reload policy under the same admission lock. Readiness
  requires both the service's current PID and its process start identity, so stale
  readiness files cannot admit tests. `start` refuses live jobs and refuses to
  lower the hard cap onto current memory use. To update kernel limits, drain jobs,
  edit configuration, then run `start` again.
- The shared server has its own reservation and lives in the persistent owner
  service. Recovery-created servers and their descendants are moved there before
  a transient job exits. Matching requires this runner's private executable,
  cache prefix, loopback endpoint and slice. Other workloads are untouched.
  Existing cgroup page charges can remain in their original group after a move.
- Existing admitted reservations are preserved when policy changes. New jobs
  wait on host headroom, aggregate reservations, host/cgroup memory pressure and
  exclusive build jobs. This runner does not automatically increase concurrency.
  It does not automatically kill or restart an idle shared pool to fit a larger
  job; explicitly drain and stop it before reconfiguring reservations.
- No default `FOUNDRY_MEMORY_LIMIT` is injected. `foundry.toml` remains authoritative
  unless the caller explicitly sets an override. Seeds, counts, filters and command
  arguments are retained. Only tool-related environment settings are persisted.
- Supplemental output is allocated inside the tested checkout, including after
  relocation. All eight stock campaign flags, including admission/composition
  requirements, are retained. No source-path aliases or campaign-specific IDs are
  needed.
- Mutation snapshots mark their build cache as private. Before implementation
  identity capture, the harness detaches any hardlinks reintroduced by CAS builds,
  verifies copied bytes and preserves modification times. Strict inode, ctime,
  source and inventory checks remain unchanged. Parent/package caches are untouched.
- The Lake adapter converts supported evaluation calls to `turbo-lean eval` and
  supports all four `main` types: `IO Unit`, `IO UInt32`, and their `List String`
  forms. Nonzero results, exceptions, malformed JSON and tool failures stay failures.
  Unsupported Lake command forms pass through to the pinned Lake executable.

The runner schedules commands; it does not certify aggregate suite coverage,
carry verdicts between revisions, or send automated chat messages. Record tested
revisions and audit required coverage separately. `stop` refuses admitted work and
stops only this runner's persistent owner service.

## Regression checks

The standard Python test discovery includes the runner unit tests. They exercise
policy refresh, stale readiness, admission accounting, process identity and worker
ownership, preserved failed attempts, output relocation, warm evaluation failures,
and real filesystem hardlink isolation.

An opt-in integration test starts a fresh user slice with a 4 GiB hard cap, runs
small Lean entrypoints and expected failures, verifies the owner survives job exits,
and stops that service. It does not run the full suite or mutation inventory:

```bash
VERITY_RUNNER_INTEGRATION_TURBO=/path/to/pinned/turbo-lean \
  python3 -m unittest discover -s scripts -p test_verification_runner.py -v
```
