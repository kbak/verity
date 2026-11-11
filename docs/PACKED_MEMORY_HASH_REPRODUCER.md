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

After PR #23 merges, move this branch onto that merged revision, implement the
generic lowering, and compare imported semantics and Verity-generated EVM output
with these unchanged expectations. Helper renaming
must preserve importer support; body changes must change the model or yield a
located rejection. Storage-key addressing and preservation of unrelated state
still need their own regressions. Full proof, smoke, loss and mutation gates
remain required before an implementation is ready to merge.
