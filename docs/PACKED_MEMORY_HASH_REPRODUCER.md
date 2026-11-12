# Packed memory hashing reproducer

This preparatory regression for [Qorrect #55](https://github.com/quantstamp/qorrect/issues/55)
starts from fork commit `0c5b5fae430a7c2772c96722f7a20e96edc37038`.
The importer fix will be based on the merged integration of
[fork PR #23](https://github.com/kbak/verity/pull/23). This change adds no importer
support, correspondence proof, or generated Verity output.

`Contracts/SolidityImportSmoke/PackedMemoryHash.sol` exercises generic overlapping
`mstore` operations followed by a 58-byte `keccak256` slice and scratch cleanup.
The independent expectation concatenates a 20-byte address, two signed 3-byte
integers in two's complement, and a 32-byte salt. It does not inspect Solidity,
the importer, generated output, or EVM observations to determine expected values.
A separate byte-memory replay checks the write overlap against that specification.

The concrete input is address `0x1234567890123456789012345678901234567890`, signed
integers `-60` and `60`, and salt `42`. Its fixed preimage is:

```text
1234567890123456789012345678901234567890ffffc400003c000000000000000000000000000000000000000000000000000000000000002a
```

Its fixed Keccak-256 digest is
`d80661cdbaa9a56d329521f782aa547f64b7e6bab5591f0eaa0477beeb91d628`.
These literal anchors are checked as well as the general field-width oracle.

## Run

Use the repository's pinned Solidity 0.8.26 installer and Foundry v1.5.0 with
`anvil` on `PATH`. The runner validates the Solidity binary's pinned checksum.
Python uses the standard library and existing repository modules.

```sh
python3 scripts/setup_solc_import.py --version 0.8.26
PYTHONPATH=scripts python3 -m unittest scripts/test_packed_memory_hash.py -v
PYTHONPATH=scripts python3 -m solidity_differential.check_packed_memory_hash \
  --output .lake/packed-memory-hash-evidence
```

The output directory must be new. `--solc /absolute/path/to/solc-0.8.26` selects
an existing checksum-verified binary without modifying another checkout.
The source profile is Cancun, viaIR, optimizer runs `44444444`, metadata hash
`none`. An owned temporary Anvil node executes the source bytecode in Cancun
and is stopped on exit. No shared node or external network endpoint is used.

The default campaign uses 54 inputs: the concrete case, all pairs of signed
24-bit boundary values, address/salt extremes, and 16 seeded random inputs.
Each input has a direct digest call and seven memory-inspection calls, for
432 calls per source variant. The inspection moves the scratch base by
0, 1, 3, 31, 32, 63, or 64 bytes and observes the digest, free-pointer delta,
three cleared words, and an adjacent canary. This is bounded scratch-memory
aliasing coverage, not arbitrary memory aliasing support.

| Source variant | Required result against the unchanged expectation |
| --- | --- |
| Original overlapping writes | Every digest and memory observation matches |
| Renamed internal helper | Every digest and memory observation matches |
| Padded `abi.encode` replacement | Every call has a different digest |
| Low-bit change to one signed field's write | Every call has a different digest |

Mutants are compiled and executed as separate Solidity contracts. They never
change the checked-in fixture or oracle. Compilation, deployment, and RPC
failures are errors; they do not count as mutation detection. The padded variant
represents the 128-byte replacement bug class. It does not execute the existing
importer's name-selected replacement.

## Importer regression preparation

The companion runner uses the same four source variants and unchanged 54-input
expectations. It independently compiles each variant with the pinned profile,
then probes `digest` and `inspect` separately using `turbo-lean --json eval`.
A scalar identity contract must import successfully first. No importer source
changes or rebase are needed to collect these observations.

Configure the pinned Turbo-Lean environment as described in `AGENTS.md`, then run:

```sh
PYTHONPATH=scripts python3 -m unittest scripts/test_packed_memory_hash_import.py -v
PYTHONPATH=scripts python3 -m solidity_differential.check_packed_memory_hash_import \
  --output .lake/packed-memory-hash-import-observations
```

The output directory must be new and inside this checkout. The runner builds
`Compiler.SolidityImport.Import`; `--prepared` may skip that build only when this
checkout's importer is already built. The compiler must be installed in this
checkout's `.lake/solidity-import` directory.

Each rejected root must have exactly one unsupported-source error with a valid
Solidity line/column and a closure containing that root. Crashes, timeouts,
missing dependencies, invalid source and additional elaboration errors fail the
run. Renaming must preserve admission or the rejection reason and closure.
Accepted imports retain the actual model, report and source digest; an accepted
body mutation must not produce the identical model as an accepted original.
Different model text alone does not establish that the changed body is correct.

Observation mode exits successfully only when collection and these controls
succeed. It does **not** require admission: `results.json` separately records
`requiredRootsAdmitted` and marks semantic agreement as untested. Add
`--require-admission` to fail until both original and renamed roots are admitted.
That option changes only the admission gate, never the byte/hash expectations.
The manifest explicitly marks Denote and generated EVM execution as not run.

The admission runner also varies the helper spelling and adds zero, one, or two
unused private storage declarations, for each original, padded, and changed body.
These 18 additional probes must preserve each body's admission or located
rejection. `--helper-name IDENTIFIER` adds another spelling to this matrix, allowing
historical dispatch names to be tested without coupling the fixture to a project.
`helper-controls.json` retains the observations even if the matrix detects a
regression. These controls do not alter the fixture, vectors, or byte/hash oracle.

On this branch's current importer, the eight probes produce seven located rejections
and one admission. Original, renamed and changed-body `digest` reject the first
overlapping write at line 18; their `inspect` roots reject the free-pointer write
at line 42. The padded `digest` imports; padded `inspect` rejects at line 31.
Each rejection reports `only scratch-space mstore at 0x00 or 0x20 is supported`.
The renamed helper preserves the same boundary. The scalar identity control
also imports. These observations leave `requiredRootsAdmitted` false.

## Evidence and remaining work

The output retains compiler requests/results, every source variant, deployment
traces, calldata, expected/actual return bytes, mutation mismatches, the independent
preimages, and a manifest with the fork revision, worktree status, source/harness
digests, compiler identity/settings, random seed, and node identity. Source edits
are identified by digests even when the worktree has not yet been committed.

The source EVM and Python Keccak implementation are execution dependencies;
this finite campaign does not prove cryptographic correctness, hash injectivity,
or Solidity/importer/compiler correspondence. No hash premise is discharged by
this test. Imported semantics and Verity-generated output are explicitly marked
**not run** in the manifest. A successful source campaign is not evidence that
Verity admits this construct or preserves its meaning.

Integration PR #23 merged as `eb5d7249c4b7aad2841da289d72b500b1a2877bc`.
[Stage 1 (#28)](https://github.com/kbak/verity/issues/28) removes the incorrect
name-selected 128-byte replacement and its registry entry. Helpers now go through
ordinary body translation. Packed-memory admission remains unsupported; this
correction adds no memory lowering and does not satisfy `--require-admission`.
The existing combined smoke model retains eight admitted roots; its ninth,
packed-hash-dependent root is checked for a located rejection instead of exposing
an incorrect model. No golden or byte/hash expectation is changed.

The remaining stages are the memory proof bridge (#29), actual three-route
execution (#30), source-driven memory lowering (#31), and storage-reference
addressing/state preservation (#32), all tracked in `kbak/verity`. Full proof,
smoke, loss and mutation gates remain required before an implementation is ready
to merge. Import coverage is not a source-correspondence proof.

## Coherent byte-slice proof bridge

The Stage 2 lemmas in `Verity/Core/Model/MemorySlice.lean` connect the actual
chunked reader used by the differential oracle to `Memory.slice` for any start
address in a coherent world. `Compiler/Proofs/IRGeneration/MemorySliceBridge.lean`
connects the proof IR's concatenated/truncated reader to the same physical bytes
when `offset + byteWordCount size * 32 ≤ 2^256`. This sufficient bound covers the
rounded word window; it excludes wrapping reads and does not require alignment.

The IR reader definitions are extracted unchanged into a small `MemorySlice`
module. The differential oracle uses the same byte-expression through a shared
definition, so the bridge targets its real input computation. The generic
write-sequence lemmas retain coherence, bytes outside every write footprint, and
all non-memory fields even when the write footprints overlap each other.

These proofs establish byte-input equality and its transport through the existing
hash function. They add no importer admission, hash injectivity assumption, or
EVM/solc correspondence claim. The unchanged admission gate remains closed until
Stage 4. Stage 2 is prepared on top of Stage 1 and must merge after it.

## Pinned three-route execution harness

Stage 3 adds `scripts/solidity_differential/check_packed_memory_hash_routes.py`.
It executes the source bytecode, the actual imported `Denote` body, and the
Verity-generated bytecode. The generic word-hash control must pass all three
routes against independently encoded bytes and a fixed zero-word hash anchor.
Admitted packed roots use the original fixture, 54 vectors, seven scratch shifts,
literal anchors, and source mutations unchanged.

With pinned Turbo-Lean, Anvil, and Solidity 0.8.26 installed:

```bash
python3 scripts/setup_solc_import.py --version 0.8.26 \
  --output .lake/solidity-import/solc-0.8.26
PYTHONPATH=scripts python3 -m solidity_differential.check_packed_memory_hash_routes \
  --output .lake/packed-memory-routes
```

Both source and generated-code compilation use the checksum-verified
`0.8.26+commit.8a97fa7a` binary and Cancun, with optimizer runs `44444444`.
The source retains viaIR and metadata hash `none`. Generated Yul uses the
optimizer directly; Solidity's viaIR and metadata options do not apply to Yul.
Verity's target is explicitly Cancun, and all routes use the real source selector
and identical static argument words. The generic Osaka runner remains unchanged.

Each EVM route deploys on a fresh Cancun node, verifies its runtime code and
empty initial balance, and calls the pure root at the deployment block.
Source ABI checks require pure functions, static returns, empty storage layout,
and no constructor. Denote receives the matching sender, origin, contract
address, timestamp, block number, chain ID, zero call value, and empty storage.
This campaign observes pure return bytes; it does not establish storage frames,
account/balance equivalence, gas behavior, or a whole-contract theorem.

The output archives exact source variants, revision and implementation hashes,
compiler identities/settings, model/report/source digest, Denote inputs/results,
Yul, creation/runtime bytecode, node identity, deployment traces, call environments,
calldata, independent expectations, and actual outputs. Inputs are embedded in
Turbo-Lean evaluation drivers; the snapshot returns JSON on stdout, so a cached
evaluation cannot silently skip artifact writes. A revision, source, or compiler
change during the campaign fails the run.

Exit `0` means the harness controls and all available route checks passed.
Rejected packed roots are still recorded as **blocked**, with no claimed semantic
agreement. Add `--require-admission` to require all original/renamed digest and
inspection roots to execute successfully; exit `1` means that admission gate is
still closed. Infrastructure errors use exit `2`. Missing observations, crashes,
timeouts, deployment failures, unexpected reverts, and RPC errors never count as
mutation detection. A mutation is detected only by complete successful executions
whose hashes differ from the unchanged independent expectations.

Stage 4 enables the bounded memory fragment and must pass this admission gate.
The later storage-reference campaign remains a separate Stage 5 obligation.
