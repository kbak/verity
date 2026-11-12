# Solidity import

`solidity_import` turns selected Solidity functions, and the helpers they
reach, into an ordinary Verity `CompilationModel`. The model runs on the same
`Denote` semantics as Verity's proofs, so theorems about it are theorems about
the imported code. The importer lives in `Compiler/SolidityImport/`; the
Midnight pilot (`lfglabs-dev/morpho-midnight-verity`) is the reference user.

## Usage

```lean
import Compiler.SolidityImport.Import

solidity_profile build where
  evmVersion := "osaka"
  viaIR := true
  optimizerRuns := some 466   -- none = optimizer off
  bytecodeHash := "none"

solidity_import example from "Contracts/SolidityImportSmoke" entry "Slice.sol" using build
  contract C
  function f(Mkt, bytes32, address)
  function lossOf(bytes32)
```

- `from` is the Solidity project directory, relative to the importing
  package's `lakefile.lean`; its `remappings.txt` resolves imports. `entry` is
  the file declaring the contract.
- `solidity_profile` defines an ordinary `Profile` value (reusable,
  `#print`able). `using` takes any `Profile`, named or inline
  (`using { evmVersion := "osaka", ... }`). The settings go to solc and into the
  digest; they should match how the audited bytecode is built. `solc` defaults
  to `0.8.34+commit.80d5c536`, and also accepts pinned 0.8.26, 0.8.10 and
  0.7.6 releases. 0.8.10 requires `viaIR := false` and `evmVersion` up to
  `"london"`; the experimental 0.7.6 boundary is described below.
- Each `function` clause selects one root by name and Solidity parameter types.
  A struct may be qualified (`IMidnight.Market`). Roots are lowered
  independently and share one field list.

The command defines `example.model`, `example.report` (`toText` renders the
reviewed inventory), `example.sourceDigest`, and the kernel theorem
`example.covered`. It works inside namespaces.

It also defines typed accessors for specifications, with Solidity types
(`UIntN n`, `Uint256`, `Address`, `BytesN 32`, `Bool`):

- Function accessors are generated only when every parameter and return type
  has a scalar Lean representation. Tuple and array signatures do not receive
  these accessors; use the full model with the public Denote entry point and
  matching raw calldata for composite ABI execution. No synthetic
  `m_maturity` argument is generated.
- `example.position.credit oracle world id user : UIntN 128` reads
  `position[id][user].credit` with the imported layout (solc's slot, word
  offset and packing); `example.position.credit_val` states that its value is
  exactly the model's read. Key binders use the Solidity key names.

`oracle` computes mapping slots and is a parameter, so a theorem over these
accessors holds for any slot derivation; it does not identify slots with Keccak.

Install the compiler once with `python3 scripts/setup_solc_import.py --all` (a
downstream package passes `--output .lake/solidity-import/solc-0.8.34` or `--version 0.8.10 --output .lake/solidity-import/solc-0.8.10`).
Elaboration never downloads a compiler; it checks the binary's SHA-256 before
and after running it.

Declare the Solidity tree as a Lake input so editing a source rebuilds the
import:

```lean
input_dir midnightSol where
  path := "vendor/midnight/src"
  filter := .extension "sol"
lean_lib MorphoMidnight where
  needs := #[midnightSol]
```

## Experimental Solidity 0.7.6 scalar subset

Select `solc := "0.7.6+commit.7338295f"` explicitly, with `viaIR := false`
and `evmVersion := "istanbul"`. Other legacy EVM targets require separate
admission and execution evidence. The official Linux and
macOS binaries are SHA-256 pinned in the importer and setup script. No pragma
is rewritten and no compiler fallback occurs. The reference fixtures use
Istanbul, optimizer disabled (`runs: 200` retained in standard JSON), and
`metadata.bytecodeHash: "ipfs"`. Other application profiles must retain their
own exact settings; this profile does not assert deployed-bytecode identity.

The initial slice admits unsigned scalar arithmetic (including narrow-width
wrapping), boolean/address/bytes32 values, unsigned/address conversions, scalar
state and mapping reads, conditionals, local assignments, and the admitted internal helper
forms. Function boundaries restore wrapping for 0.7.6 and checked arithmetic
for 0.8; an explicit 0.8 `unchecked` block does not leak into a helper. In
particular a wrap-then-`require` idiom must evaluate the wrapped result before
its explicit guard. The additional declaration gate is conservative and runs
on roots and reached helpers; existing construct checks still apply. Functions
may be `pure`, `view`, or `nonpayable`; the state-transition extension below
adds scoped write/modifier/event evidence. Named payable entrypoints are covered by
the explicit value-transaction extension below.

### Legacy state transitions

The legacy boundary admits nonpayable functions, reached single-placeholder
modifiers, unsigned/address scalar and mapping writes, wrapping increments and
compound assignments, and scalar events through the existing lowering. Reached
modifier declarations receive the same legacy AST and division-path checks as
functions; internal calls restore the legacy arithmetic default. `address(this)`
retains the current contract address when converted from its contract type.
Arbitrary external writes, raw `sstore` assembly, general arrays,
assertions and unguarded division remain rejected. This is a supported construct
subset, not general 0.7.6 support.

`LegacyStateTransitions.sol` and `check_legacy_state_transitions.py` compare
source EVM, imported Denote and generated EVM sequences against independently
specified storage, ordered log topics/data and exact revert bytes. Cases cover
self-sender restrictions, zero/upper bounds, no-op writes, indexed address events,
nested calls that fail after writes/logs, ABI-v1 dirty scalars, narrow/wide wrapping,
and unrelated storage canaries. Storage-free and single-field variants exercise
helper modifiers and post-body modifier writes. Dirty packed-word preservation and
maximum-count initial worlds are primitive-semantics checks; those worlds need
not satisfy a downstream invariant.

These state-transition experiments use zero-value call frames. The default runner
still rejects nonzero value without the explicit envelope below. Former payable
rejection fixtures now require successful admission; value behavior has its own
independent runtime campaign. Self-sender experiments
explicitly impersonate the contract only on local test nodes. They check a supplied call frame; they do not prove that an authorized
transaction reaches that frame. Deployment initialization, signatures and proxy
reachability require downstream evidence. Finite observations do not prove
source/model correspondence, whole-world frames or arbitrary-sequence invariants.

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_state_transitions \
  --output .lake/legacy-state --dirty-mappings
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_state_transitions \
  --kind scalar --context 2 --optimized --output .lake/legacy-scalar
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_state_transitions \
  --kind stateless --output .lake/legacy-stateless
python3 scripts/solidity_import_mutations.py --task legacy-state-transitions \
  --task legacy-state-rejections
```

For concurrent runs in one checkout, first build `Compiler.SolidityImport.Import`,
`Compiler.SolidityImport.Differential` and `Compiler.SolidityImport.SequenceRunner`
for the exact candidate with `turbo-lean build`, then pass `--prepared`. Do not
edit or build while execution workers run. The implementation snapshot check
remains active and rejects artifact replacements even when content is identical.
Default runs build their prerequisites automatically.

The mutation task requires an unchanged passing control and all-three-route
violations of the independent requirement when self-context, zero/upper bounds or
a mapping-link update is removed from the fixture. Those are source defect
controls, not compiler mutations or discovered vulnerabilities. Build failures
and timeouts never count as detections.

ABI coder v1 is the 0.7.6 default. Scalar calldata words are cleaned to their
type rather than rejected for noncanonical upper bits; boolean words normalize
to zero or one. `pragma experimental ABIEncoderV2` and `pragma abicoder v2`
select validation in the target contract's source unit. Inherited functions
use the target contract's decoder, even when their defining file selects the
other coder. Except for ABI coder v1 bytes and address arrays described below, dynamic and
aggregate ABI, signed arithmetic, enum storage,
narrow fixed-bytes root ABI, general assembly, and general external calls
remain outside the legacy slice. Builtins are limited to `require`, `revert`, and
the `ecrecover` extension described below.
The fixed-byte and terminal memory-revert extension below admits additional
local/helper conversions and a bounded assembly form.
Division and modulo require the path evidence described below: 0.7.6 can
execute `INVALID`, whereas 0.8 emits a panic payload. Legacy assertions and
divisions without sufficient guard evidence remain rejected. Neither empty
`REVERT` nor a 0.8 panic is substituted for an exceptional halt. These are support boundaries, not claims that the
rejected source is incorrect.

Run the reusable execution campaign and semantic mutations:

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy --output .lake/legacy-run
python3 scripts/solidity_import_differential.py --mutations \
  --mutant import-legacy-root-checked --mutant import-legacy-helper-checked \
  --output .lake/legacy-mutants
```

The campaign compares original 0.7.6 bytecode, the imported Denote model, and
Verity-generated bytecode. Source compilation targets Istanbul; model Yul uses
0.8.34/Osaka and all bytecode executes on Foundry's Osaka EVM. The retained
manifest identifies both compilers. Gas, historical-fork equivalence, and
source/deployed-bytecode equivalence are not established. Dirty scalar calldata
is exercised for both ABI coders. Each mutation requires an agreeing positive
control and a concrete semantic divergence; build failures/timeouts are errors.

### Legacy address arrays and bounded traversal

ABI coder v1 `address[] memory` inputs, internal parameter forwarding, explicit
`new address[](length)` locals, indexed reads/writes, and single-array returns
are admitted. Decoding preserves the pinned compiler's inclusive 32-bit offset
and length limits, empty reverts on malformed tails, overlapping/unaligned tails,
and raw memory words. High-level reads and stores clean addresses. ABI-v1 array
returns copy raw words: untouched dirty words from calldata remain dirty.
The [0.7.6 memory-array encoder](https://github.com/ethereum/solidity/blob/v0.7.6/libsolidity/codegen/ArrayUtils.cpp#L319-L366)
uses a memory copy, not per-element address cleanup.

Allocation rejects an element count above `2^64 - 1` with an empty REVERT. It
zeroes each allocated cell. It does not substitute modern panic codes or the
modern end-pointer limit. See the
[pinned allocation implementation](https://github.com/ethereum/solidity/blob/v0.7.6/libsolidity/codegen/ExpressionCompiler.cpp#L973-L1017).
Every indexed access checks its bound and emits the closed `SolidityInvalid`
transport on failure. Denote carries a distinct `invalid` outcome through loops
and statement lists; frame completion restores the complete entry world, with
empty return data. `ExceptionalHalt.lean` proves termination, no continuation,
rollback, and the emitted instruction. These are model-level lemmas, not a
Solidity frontend or compiler-equivalence proof.

Address traversal is admitted only for `while (cursor != CONSTANT_SENTINEL)`
with exactly three statements: `items[index] = cursor`, a cursor assignment,
and `++index`. The cursor expression cannot change the index. The writable
uint256 index must start at zero, and the memory
array reference cannot be rebound. The lowerer executes at most `length + 1`
guarded iterations: a long list or cycle reaches the original failing array
write. Reaching the sentinel earlier leaves a zero-filled tail. No linked-list
invariant or reachability assumption is silently imported. Other loop shapes,
nonconstant sentinels, whole-array rebinding, tuple array writes, uninitialized reference locals,
calldata arrays, other element types, array assembly references, and ABI coder v2
arrays remain rejected. A return requires an existing memory reference.

`LegacyAddressArrays.sol` retains the initialization checks. The new generic
`LegacyMemoryArrays.sol` checks allocation, direct/helper reads, writes, returns,
independent loop bounds, and traversal. The oracle compares source bytecode,
actual Denote, and generated bytecode, including dirty words, malformed ABI,
rollback after storage writes/events, cycles, missing sentinels, and excess
capacity. Intentional source defects must violate unchanged expectations on all
three routes. The EVM adapter accepts INVALID only with a matching top-level
opcode trace and consumed transaction allowance; out-of-gas and other
unclassified failures remain harness errors.

These are finite zero-value call-frame checks. The gas-free model records the
exceptional halt kind but does not calculate opcode gas, establish gas adequacy,
or prove source correspondence or reachable initialization. Guarded no-op
iterations after the sentinel can have different gas costs. No project axiom
is added; the closed transport's compilation boundary remains assumed.

```bash
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_memory_arrays \
  --output .lake/legacy-memory-arrays
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_memory_arrays \
  --optimized --context 2 --errors cycle --output .lake/legacy-memory-cycle
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_memory_array_mutations \
  --output .lake/legacy-memory-array-mutations
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_array_rejections \
  --output .lake/legacy-array-rejections
```

### Legacy calldata copying, scalar enums and scratch hashing (experimental)

ABI-v1 `bytes calldata` root parameters retain their decoded offset and length
without allocating memory. Both have inclusive 32-bit bounds, and the complete
byte range must fit calldata. Malformed entry data reverts with zero bytes.
ABI-v1 decodes enum arguments as their unsigned integer representation (8 bits
for the admitted 1–256 members), without checking the member count. Assembly
therefore observes truncated out-of-range ordinals. Explicit unsigned-to-enum
conversions clean the source width and check the member bound; enum-to-unsigned
conversions and single unnamed enum returns also check the bound at use. These
checks execute `INVALID`, not a modern panic or empty revert. Enum locals,
assignments, conditionals, direct mapping keys, helper returns, named/multiple enum
returns and enum storage remain rejected. Comparisons and internal-helper inputs
are admitted by the raw-call extension below.

Straight-line assembly may copy calldata, read/write words and hash bytes at
the free-memory pointer or a constant nonnegative displacement of at most
`2^32`. Pointer aliases and reassignment are tracked structurally. Writes to
existing allocations, allocator metadata, variable destinations, Yul control
flow and external effects remain rejected. `calldatacopy` preserves untouched
destination bytes and zero-fills reads past calldata. It lowers to byte-preserving
physical-memory stores. Hashes observe the exact physical bytes, including unaligned regions and stores whose value hashes the
memory that they subsequently overwrite. This slice does not advance the free
pointer; a later Solidity allocation can reuse the temporary region.

Assembly can read unassigned external narrow scalar parameters: ABI-v1 cleans
unsigned/address/bool words and enum integer representations at entry. Arbitrary
narrow locals and helper parameters still require literal bindings. This is not
general dirty-bit tracking. Calldata indexing, aliases/reassignment, helper-call
arguments, slicing,
ABI-v2 bytes, dynamic ABI encoding, payable entry points and general execution
assembly remain outside this slice.

The generic runtime oracle independently constructs ABI/hash inputs, checks
byte-exact memory, malformed tails, enum failure kinds and watched storage.
Partial final calldata words retain their exact byte length in both public and
traced Denote execution; right-zero padding cannot fabricate available bytes.
Compiler mutants perturb source offsets, lengths, hash lengths, entry enum
checks and exceptional conversion outcomes. Passing controls are required;
build failures do not count as detected mutations. These finite comparisons
exclude gas/resource exhaustion and do not prove universal source equivalence.

```bash
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_calldata_hash \
  --output .lake/legacy-calldata-hash
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_calldata_rejections \
  --output .lake/legacy-calldata-rejections
```

The pinned [ABI-v1 decoder and enum conversion implementation](https://github.com/ethereum/solidity/blob/v0.7.6/libsolidity/codegen/CompilerUtils.cpp)
is the semantic reference. Public fixtures and lowering recognize language
constructs; downstream transaction schemas are not embedded in the compiler.

### Fixed-byte conversions and memory reverts (development)

The legacy extension admits `bytes1` through `bytes32` as local and helper
values. Supported conversions preserve left alignment: string/hex/UTF-8 literals
of at most N bytes become `bytesN` with right-zero padding; fixed-byte widening
retains those bytes and narrowing discards bytes on the right. Unsigned integer
conversions require the same bit width as the fixed-byte type. Explicit zero and
width-matched hex integer literals are also supported. The shared lowering keeps
`bytes20`/address conversions and applies to the supported modern compiler too.
Implicit conversions at helper boundaries use the resolved parameter type;
string arguments for actual string/bytes-memory parameters keep their existing
buffer behavior.

A straight-line legacy assembly block may declare locals, load the free pointer
at `0x40`, add word offsets, write memory words and terminate with `revert(offset,
size)`. Other assembly control flow, storage/call effects and arbitrary loads
remain rejected. The shared memory-revert transport preserves every byte of the
requested slice, including unaligned offsets/lengths, overlapping stores, empty
payloads and zero-filled memory. It never replaces a nonempty payload with an
empty revert. This terminal-revert path remains separate from the free-pointer
scratch-memory continuation described above.

Assembly may observe dirty padding in narrow values, as described by the
[0.7.6 assembly rules](https://docs.soliditylang.org/en/v0.7.6/assembly.html#things-to-avoid).
This slice therefore requires narrow scalar references in a memory-revert
block to have a literal model binding; dynamic/truncated narrow values are
rejected. General dirty-bit tracking and narrow root ABI decoding are separate
work. Fixed-byte indexing remains rejected under 0.7.6 because its out-of-bounds
behavior can execute `INVALID`.

`FixedBytesMemoryRevert.sol` and `check_fixed_bytes_reverts.py` exercise all 32
widths, literal/helper conversions, exact `Error(string)` payloads and raw memory
slices. The same source runs with zero, one and two storage fields under 0.7.6 and
0.8.34. Each execution compares original bytecode, Denote and generated bytecode,
then checks a separate byte-oriented expectation. Negative fixtures retain the
legacy admission boundary and the dirty-padding counterexample.

Full-word `bytes32`/`uint256` casts preserve the original value expression,
including its evaluation prelude. `FixedBytesCustomError.sol` checks both cast
directions in custom-error arguments under 0.8.34, with exact selector and word
payload comparisons. Narrow casts still shift or mask as required; custom-error
argument admission is unchanged.

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_fixed_bytes_reverts \
  --jobs 3 --output .lake/fixed-bytes-reverts
python3 scripts/solidity_import_mutations.py --jobs 4 \
  --task import-fixed-bytes-literal-alignment --task import-fixed-bytes-truncation \
  --task denote-memory-revert-empty --task ecm-memory-revert-size
```

`DenoteMemoryRevert` proves the exact payload formula and emitted Yul instruction
shape. The closed module rejects metadata mismatches and adds no Lean axioms.
Its ECM proof status remains `assumed`: these local facts and finite execution
checks are not an end-to-end Solidity/EVM correspondence proof. The existing gas,
fork and source/deployed-bytecode limits above still apply. This extension
does not establish signature recovery or external validator support. Memory-byte
decoding is a separate extension described below.

### Legacy memory-byte decoding (development)

Under the explicit 0.7.6 profile, ABI coder v1 `bytes memory` parameters are
materialized in parameter order at the free pointer. The decoder checks the
complete root head, the inclusive `2^32` offset/length limits and the tail bounds.
Decode failures use empty `REVERT`. Each object contains a length word followed
by the bytes; allocation rounds the payload up to 32 bytes. A zero word is
written immediately after the actual payload, matching solc's `calldatacopy`
followed by `mstore(end, 0)`, including when calldata padding is dirty. These are
legacy-specific checks; the modern decoder is unchanged.

Existing buffers can pass through memory aliases and internal helpers with
scalar or multiple scalar returns. Straight-line assembly can declare scalar
locals, assign scalar outputs, and use `add`, `sub`, `mul`, `byte` and supported
`mload` forms. `mload(add(buffer, offset))` and its reversed operand order admit
dynamic word offsets. Offsets refer to the length header, and arithmetic wraps
modulo `2^256`. Reads use physical memory, preserving unaligned words, padding,
and adjacent allocated objects. Assembly adds no logical buffer bounds check;
callers must supply bounds when their application requires them. Reading a narrow
Solidity scalar from this assembly remains rejected unless it has a literal
binding, because the high-level value alone does not determine dirty bits.

This slice rejects ABI coder v2 byte parameters (allocation failures may execute
`INVALID`), calldata/storage byte sources, byte allocation/encoding, dynamic-byte
returns, high-level byte indexing, memory writes in a
continuing assembly block, and assembly control flow. General EVM gas/memory
expansion and exceptional halts remain outside the execution model. Tests use
small final addresses, including wrapped arithmetic that returns to ordinary
memory; enormous reads are not supported evidence. The existing read-only
adapter represents complete calldata words, so partial-word calldata truncation
is not covered by this campaign.

`LegacyByteMemory.sol` exercises packed record decoding and alias/neighbor reads
with zero, one and two state declarations. The independent byte-array oracle in
`check_legacy_bytes.py` checks all three execution routes, malformed ABI heads and
tails, dirty padding, unaligned offsets, and modular pointer arithmetic. Negative
fixtures enforce the remaining admission boundary. Mutation controls change the
header adjustment, padding clear and byte lane; compilation failures do not count
as detected semantic mutations.

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_bytes \
  --jobs 2 --rejections --output .lake/legacy-byte-decoding
python3 scripts/solidity_import_mutations.py --jobs 3 \
  --task import-legacy-bytes-header --task import-legacy-bytes-padding \
  --task import-legacy-bytes-byte-lane
```

This remains an experimental import/Denote execution slice. Finite differential
checks do not establish universal source/compiler correspondence or authorization
properties for a signature-checking application. Recovery and external validation have the bounded extension below; full
application authorization still requires downstream integration and proofs.



## Legacy bounded loops and guarded division

The 0.7.6 path admits zero-based `uint256` loops of the form
`for (uint256 i = 0; i < bound; ++i)` and
`for (i = 0; i < bound; ++i)` with an existing writable scalar counter.
The bound must satisfy the existing invariant-bound lowerer, and the body must
not assign the counter or the bound (including a byte buffer supplying `.length`).
The existing-counter form executes its initializer even for zero iterations and
leaves the counter equal to the bound on normal completion. Nested counted loops,
root early returns, explicit reverts, and scalar helper calls retain their normal
control flow. Helper-loop early returns remain unsupported.

Unsigned `while (v != 0)` / `while (v > 0)` loops use the existing exact
bit-clearing or positive constant right-shift progress checks. The lowering runs
at most the operand's bit width, testing the source condition at each iteration.
The legacy admission gate excludes other while forms, including modern lowering
paths that use heuristic iteration limits. General loops, `do` loops,
`break`/`continue`, narrow for counters, inclusive for bounds, and mutations of
the loop counter from its body remain rejected.

Unsigned `/`, `%`, `/=`, and `%=` are admitted only for a positive integer literal
or an unsigned local/parameter whose nonzero value follows from a guard on every
reaching path. The analysis understands `require`, zero comparisons, negation,
short-circuit conjunction/disjunction, and early `return`/builtin `revert`.
For example, `if (a == 0) return 0; uint256 c = a * b; require(c / a == b);`
uses wrapped multiplication followed by the source's explicit overflow check.
The guarded denominator must never be assigned in that reached declaration;
the analysis includes compound assignments, loop updates, and assembly writes.
Each reached helper establishes its own guards. Casted/computed denominators,
state-derived guards, caller-only guards, and guards invalidated by assignment
are conservatively rejected. This is an admission analysis, not a general
nonzero solver or a proof of source/compiler correspondence.

`LegacyControlFlow.lean` implements this boundary and contributes to the importer
source digest. Once admitted, division/modulo lower to unsigned EVM arithmetic;
no modern panic is inserted for the excluded zero case. Legacy `require(bool)`
preserves empty revert bytes regardless of unrelated state declarations. Modern Solidity's
division-by-zero panic behavior is unchanged.

`check_legacy_control_flow.py` compares the actual solc 0.7.6 bytecode, executable
model, and compiled model with independent integer/byte formulas. It exercises
zero iterations, final counter values, nested and shrinking loops, narrow
wrapping, multiplication overflow, guarded division/remainders, exact explicit
revert bytes, and repeated memory decoding inside loops. It repeats the generic
fixtures in separate source inputs with zero, one, and two storage declarations
(including imported files); `--optimized` also checks
the optimized source profile. Rejection controls include stale guards, partial
paths, loop-carried writes, narrow casts, and unstable loop bounds.
The guard-stability admission mutation must expose a successful import of a
forbidden program (`require(b != 0); b--; return a / b`, with `b = 1`). It does
not classify exceptional halts as ordinary execution results. Separate execution
mutations corrupt division operands and the final loop counter; all mutations
require passing positive controls, and build/import failures never detect them.
A modern regression retains the exact division/modulo-by-zero panic payload.

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_control_flow \
  --jobs 4 --rejections --guard-probe --modern --output .lake/legacy-control-flow
python3 scripts/solidity_import_mutations.py --jobs 3 \
  --task import-legacy-loop-final-counter --task import-legacy-division-operands \
  --task import-legacy-guard-stability
```

The finite campaigns exercise small counted loops and word-bounded shrinking
loops. They establish neither gas equivalence nor success for resource-exhausting
executions. Exceptional halts remain outside the model. The admission mutant
checks rejection without executing the exceptional halt. The calldata-word adapter and
memory limits described above still apply. Full signature checking still needs
cryptographic and external-contract integration, among other construct gaps.

Semantic references: [Solidity 0.7.6 control structures](https://docs.soliditylang.org/en/v0.7.6/control-structures.html)
and [integer arithmetic](https://docs.soliditylang.org/en/v0.7.6/types.html#integers).

## Proving properties of an imported function

State properties with the typed accessors above. The accessors unfold to
`runFunction` and `readMember` (`Compiler.SolidityImport.Access`), and
`evalExpr_structMember2_param` rewrites the model's own storage reads to
`readMember`. `Compiler.SolidityImport.Proofs` provides the lemmas used to
reason about the execution: word arithmetic (`sub_word`,
`mul_word128`, `div_word`, `mask_eq`), bindings (`lookup_bind_same`,
`lookup_bind_other`), and splitting a body into straight-line parts
(`split_prefix`, `list_frame`, `ends_return`). Solidity locals keep their name
in the model, so a proof can refer to `postSlashCredit` rather than to a
generated temporary. See
[morpho-midnight-verity](https://github.com/lfglabs-dev/morpho-midnight-verity)
for a complete example.

## Supported Solidity

The importer accepts the following constructs in a resolved function closure.
Other constructs fail with a located diagnostic; this is not general Solidity support.

| Construct | Lowering |
| --- | --- |
| Multiple selected entry points | One model with independently resolved root closures |
| `msg.sender`, `address(this)` | Dedicated caller and current-contract expressions, resolved by solc builtin declaration ids |
| `block.timestamp`, `block.number`, `block.chainid`, `block.basefee`, `tx.origin`, `tx.gasprice`, `address(this).balance` | Dedicated transaction- and account-context expressions (`Expr.blockTimestamp`, `Expr.blockNumber`, `Expr.chainid`, `Expr.baseFee`, `Expr.txOrigin`, `Expr.gasPrice`, `Expr.selfBalance`), including `payable(address(this)).balance` and Yul `selfbalance()` / `origin()` / `basefee()` / `gasprice()` |
| Ordinary nested root blocks | Ordered recursive lowering with unique local bindings, lexical lookup restoration, and propagated unconditional returns; unsupported nested control flow and statements after return reject with source locations |
| Explicit scalar/tuple return | `returnValues`, preserving order |
| Default scalar locals (development; validation pending) | Uninitialized unsigned integers, address, bool and bytes32 bind a fresh local to zero; reference and unsupported scalar defaults reject at the declaration |
| Scalar local writes (development; validation pending) | `=` and `delete` on materialized scalar locals; converted RHS evaluated before assignment; lexical shadowing retains declaration identity; compound writes and parameter writes reject |
| Invariant scalar `for` (development; validation pending) | uint256 counter from zero, strict `<`, increment by one; literal/parameter/unwritten-local bounds; body return/revert preserved; body counter writes, mutable bounds, break/continue reject |
| Empty `revert()` and ABI rejection payloads (development; full release gates pending) | Explicit `Stmt.revertEmpty` compiles to `revert(0,0)` and Denote observes exactly zero bytes, independent of memory and the current return-data buffer. Source scalar/struct guards, getter bounds and bare builtin revert keep their existing conditions and source-position rejections. Other external calls remain outside admitted source support. |
| Typed-interface word staticcall (development; full release gates pending) | `I(addr).f(args)` where `f` is a `view` function of an interface whose parameters are `address`, `uint256`, `bytes32` or `bool` and which returns one `uint256`, `bytes32` or `bool`, `addr` has type `address`, each argument has its parameter's type (or is a non-negative integer constant for `uint256`) and lowers without prelude statements, and the call is a whole single-variable initializer, the right-hand side of `=` to an identifier, an expression statement, the condition of a builtin `require`, or (recursively) an operand of a short-circuit `&&`/`\|\|` in one of those positions. Lowers to the closed `SolidityStaticCall.uint256Module` ECM: selector and cleaned argument words (`address` masked to 160 bits, `bool` normalised to `0`/`1`) stored at the free pointer, `staticcall(gas(), addr, p, 4 + 32n, p, 32)`, a failed call's complete return data forwarded as the revert payload, fewer than 32 success bytes revert with no data (including accounts without code), the first word decoded and extra bytes ignored; a `bool` result other than `0`/`1` then reverts with no data, as solc's ABI decoder does. Short-circuit operands keep the call inside the branch Solidity evaluates; a `require` condition, call included, is evaluated before the error arguments, matching via-IR. Denote executes the same request against an explicit byte adversary. Non-view/pure callees, other parameter types (narrow integers, `address payable`, `bytesN<32`, dynamic and struct parameters), other return shapes, mismatched or side-effecting arguments, named arguments, call options, non-interface receivers, `address payable`/typed-local receivers, `return`/`if`-condition/`!`/comparison/conditional/compound/indexed-target/error-argument/nested-argument placement and `try` reject with `file:line:column`. `InterfaceStaticCallSequence` (parameterless `uint256`) and `InterfaceWordStaticCallSequence` (word arguments, `bool`/`bytes32` returns, short-circuit and `require` placement) each run three equivalent variants A/B/C, against selector-checked and calldata-folding oracle mocks respectively, plus an account without code. |
| SSTORE2-style `create2` code storage (development; full release gates pending) | Yul `create2(0, add(buf, 0x20), mload(buf), salt)` (offset operands in either order) as the whole value of a Yul assignment or `let`, in roots or inlined helpers, where `buf` is an unshadowed, never-reassigned `bytes memory` local initialised by `abi.encodePacked(p, ...)` or `bytes.concat(p, ...)` and `p` is a hex literal (or constant) whose bytes start a checked `DenoteCreate2.templateCost` initcode template. Lowers to the closed `SolidityCreate2.module` ECM: the compiled model emits `create2` over its own memory, and Denote runs `Create2Opcode.execute` on the frame's physical byte memory with the instrument-supplied parent gas, binding the created address or zero and committing code, nonces and balances to `ContractState.accountWorld`. Nonzero/computed values, other offsets, sizes or buffers, unchecked prefixes (including other SSTORE2 prefixes), nested `create2` and `create` reject with `file:line:column`. |
| Struct event parameters (development; full release gates pending) | `emit E(...)` whose non-indexed parameters include a struct passed as a memory struct variable, alongside indexed value-type parameters (`uint*`, `address`, `bool`, `bytes32`). The non-indexed arguments are encoded exactly as `abi.encode(...)` (dynamic struct members included) and logged by the closed `SolidityLog.module` ECM with solc's `eventSelector` as topic 0 and cleaned indexed topics; Denote reads the payload from physical memory. Indexed structs, narrow fixed-bytes/enum/dynamic indexed parameters, struct constructors and storage structs as arguments, and anonymous events reject with `file:line:column`. `Create2BytecodeAndStructEmitSequence` runs three equivalent variants A/B/C with trace-discovered deployment accounts. |
| `<address>.code.length` and optional-bool low-level `.call` (development; full release gates pending) | `<addr>.code.length` on an `address`-typed account other than `address(this)` lowers to the closed `SolidityExtCodeSize.module` ECM (`extcodesize`); Denote reads `DenoteExternalCode.extCodeSize` over `ContractState.accountWorld`. The Solady/OpenZeppelin `SafeTransferLib` sequence `(bool success, bytes memory returndata) = target.call(abi.encodeCall(f, (args...)));` `if (!success) { assembly { revert(add(returndata, 0x20), mload(returndata)) } }` `require(returndata.length == 0 \|\| abi.decode(returndata, (bool)), reason);` in roots and inlined void helpers, where `f` is an external function whose parameters are `address`, `bool`, `bytes32` or `uint256`, lowers to the closed `SolidityLowLevelCall.optionalBoolModule` ECM followed by the same `reason` check of its result: the value-free `CALL` of `selector ++ words` written at the free pointer (advanced after the call), a failed call's complete returndata forwarded, empty returndata accepted, non-empty returndata shorter than a word or whose first word is not `0`/`1` reverting with no data, and a decoded `false` failing `reason`. Denote issues `DenoteByteExternalCalls.callBytesRequest` to the explicit byte adversary and keeps its committed world; `DenoteLowLevelCall` relates the result to `decodeOptionalBoolCall`. Call options (`{value: ...}`, `{gas: ...}`), unbound or unvalidated returndata, missing forwarding, strict or other validations, other reads of `success`/`returndata`, non-`abi.encodeCall` or dynamic-parameter calldata, stateful operands, other placements (expression statements, helpers with returns), `staticcall`/`delegatecall`, `address(this).code.length` and other `.code` reads reject with `file:line:column`. `ExternalCodeAndLowLevelCallSequence` runs three equivalent variants A/B/C against recording call responders, an account without code and an EOA. |
| `<address>.code` and dynamic-struct `abi.decode` returns (development; full release gates pending) | `<addr>.code` on an `address`-typed account other than `address(this)`, as the `bytes` operand of `abi.decode` or the initializer of a `bytes memory` local, lowers to the closed `SolidityExtCodeCopy.module` ECM: solc's `external_code_at` (`extcodesize`, a fresh `bytes memory` allocation at the free pointer with `Panic(0x41)` on 64-bit overflow, the length word, then `extcodecopy`); Denote copies `DenoteExternalCode.accountCode` from `ContractState.accountWorld` into physical memory. `abi.decode(data, (S))` from a `bytes memory` buffer, where `S` is not flat and its complete `AbiSchema` holds only unsigned scalars and dynamic arrays of unsigned scalars or of flat scalar structs, materializes `S` in solc's memory layout (`AbiMemoryDecode`: solc's `abi_decode_*_fromMemory` checks, eager `Panic(0x41)` allocation, zero-byte revert for every other malformation) as a single `S memory` local or a root return value. Roots with an unnamed `returns (S memory)` for such an `S` return `abi.decode(...)` or a memory struct variable with a complete schema (including `S memory` parameters): the struct is re-encoded by the shared `abi.encode` lowering and returned by the closed `SolidityReturnMemory.module` ECM (`return(ptr, size)`); Denote stops with the buffer's words in `observedReturnWords`. `address(this).code`, other `.code` uses (`keccak256(a.code)`, `a.code[i]`), calldata sources, extra decode targets, `bytes`/nested-struct/fixed-array members, named returns, calldata-struct and helper-call returns, reassigned decoded locals, member access on a decoded value and tuple returns reject with `file:line:column`. `ExtCodeCopyStructDecodeSequence` runs three equivalent variants A/B/C over code stored by the checked CREATE2 transport, including malformed payloads. |
| Schema ABI array-length `for` (development; validation pending) | Memory/calldata array length captured after its exact initial decoder; recursively checked body preserves memory headers; memory writes and external calls reject |
| Local declarations and storage aliases | Bindings named after the Solidity local (suffixed `_1`, `_2`, ... on collision), or resolved read paths |
| Scalar storage reads, `=`, and `delete` | Resolved uint8–uint256, address, bool, and bytes32 fields; exact solc slots and packed offsets; masked writes preserve neighboring bits and bool reads/writes normalize to 0/1 |
| Root fallthrough, bare `return;`, and named root return parameters | Void roots emit `stop` on fallthrough or bare `return;`; roots whose return parameters are all named scalars initialize each to zero, allow body reads/writes, and emit `returnValues` on bare `return;` or fallthrough; empty-body scalar hooks return zero words |
| One/two/three-key mappings to structs | solc slots, word offsets, and packed uint offsets (three-key mappings hash the outer two keys via `keccak256(abi.encode(k2, keccak256(abi.encode(k1, slot))))`) |
| One/two/three-key scalar mappings | address/uint256/bytes32/int256/bool/enum keys; uint8–uint256, int256, address, bytes32 and bool values; root assignment and `delete`, with masked narrow writes |
| Events | Resolved non-anonymous scalar events, including qualified library declarations, up to three indexed arguments and exact source-order data. Arguments must have total scalar preludes. Narrow unsigned event arguments require either a direct parameter of the declared type or an in-range canonical integer constant literal (`n < 2 ^ bits`); anonymous/dynamic events, named arguments and conflicting declarations reject with source locations. |
| Short-circuit boolean expressions and `!` | `&&` and `||` evaluate the left operand once; the right operand, including guards and helper preludes, executes only in its selected branch. Prefix `!` on a `bool` operand lowers to `Expr.logicalNot`. Unsupported constructs still reject even in unreachable operands. |
| `if` / `else` statements | Root statements lower to `Stmt.ite` on a boolean condition evaluated once; a branch `return` or `revert` stops execution and the continuation runs only on fallthrough. In inlined single-value helpers, the continuation after a returning branch is lowered once into the other branch and both results assign one fresh local; in inlined void and multi-return helpers, nested early `return` inside `if`/`else` lowers the post-conditional continuation into the fallthrough branch(es) after restoring branch-local lexical scope. Unsupported constructs still reject in unreachable branches. |
| Numeric literals and units (development) | Exact integral decimal/scientific/hex literals, including leading-dot fractions and digit separators, unsigned/bool named constants, and bounded sums of exact natural constant operands; seconds, minutes, hours, days, weeks, wei, gwei, ether. Fractional results, oversized words and general rational constant expressions reject. Focused checks pass 96 A/B/C transactions, 56 acceptance/rejection controls and 16 semantic mutants with minimal witnesses; the numeric parent `b0fa7b0e2` passed all 12 exact-head gates. |
| Exact natural constant products (development) | `int_const` multiplication of two lowered natural literals with empty preludes uses unbounded arithmetic and requires a uint256 result. Includes `100 * 365 days`; fractional operands, oversized intermediates and general rational operations reject. Focused checks at `bbc8fe0ad` pass 96 A/B/C transactions, 60 acceptance/rejection controls and a product mutant with a replayed minimal witness; full exact-head gates pending. |
| Inline constant array reads (development) | A directly indexed unsigned fixed array of exact natural constants lowers to a bounds guard (panic `0x32`) and value selection. Named constants are supported; nonconstant/guarded elements, other element types and escaping array values reject. Focused checks at `674cd89cd` pass 96 A/B/C transactions, 67 acceptance/rejection controls and three detected mutants with replayed minimal witnesses; full exact-head gates remain pending. |
| Unsigned modulo (development) | Typed unsigned `%` uses EVM remainder after a zero-divisor guard that panics with code `0x12`; narrow operands retain their declared unsigned width. Signed `%` is the `int256` row of the signed slice below. General constant/rational modulo rejects. Validation pending. |
| ABI array length (development, unvalidated) | Candidate `.length` lowering for schema-checked scalar or flat static-struct arrays inside memory/calldata struct parameters. Memory uses the materialized header; calldata checks the lazy header at source access. A/B/C fixtures, malformed inputs and two mutants are prepared; native validation and release gates remain pending. Storage arrays and other schemas remain unsupported. |
| Scalar ABI canonicality | Raw `uintN`, address and bool words are checked before source execution, including unused parameters. Noncanonical words revert with empty bytes. Complete-word A/B/C checks exercise mixed parameter positions; dynamic struct and partial-byte ABI validation remain outside this instrument. |
| Boolean literals | Resolved `true`/`false`; canonical 1/0 values |
| Flat static memory/calldata struct parameters | Full tuple ABI including unused scalar members; indexed field bindings and complete head sizes. Memory members are validated at entry; calldata members are validated when read, preserving competing reverts. |
| Dynamic memory/calldata structs (experimental) | Complete unsigned-scalar roots with dynamic scalar arrays or arrays of flat scalar structs. Full ABI signature, eager memory materialization and lazy calldata reads; direct element indices only. No legacy member projection. Mixed static/dynamic struct parameters and computed element indices reject precisely. Permanent fixtures cover a multi-file imported nested dynamic struct (`NestedDynamicStructAbi`, 408 A/B/C controls, four variants), scalar arrays (96 controls, three variants), and two dynamic roots (132 controls, four variants). Twenty dynamic ABI mutations are detected and minimized. Generated-name collision is checked against the actual decoder binding. Whole-library proof compatibility passes; exact-head campaign gates remain pending. |
| Unsigned `+`, `-`, `*`, `/` | Word arithmetic with overflow/underflow/zero-divisor panics |
| Unsigned comparisons, equality | Scalar conditions |
| `require(condition, "message")` | Exact `Error(string)` bytes; UTF-8 literal messages, including empty strings, in roots and inlined helpers |
| `require(condition, CustomError(args))` and `revert CustomError(args)` | Resolved static unsigned/address/bool/bytes32 errors; arguments restricted to decimal numeric literals or scalar bindings; exact selector and ABI words (`revert CustomError(args)` lowers to `.requireError (.literal 0) name values`) |
| Narrowing casts | Bit masks, not overflow checks |
| Ternaries | Lazy `ite` branches |
| Resolved acyclic helper calls | Inlined single-value, void, and multi-return internal/private bodies with separate local scopes, including C3 virtual override resolution across `linearizedBaseContracts`, diamond `super.fn(...)` resolution, explicit base-qualified `Base.fn(...)` calls, and empty-body scalar virtual hooks |
| ABI encoding and Keccak (experimental) | `keccak256` over static scalar `abi.encode`, a single complete supported root struct, literal byte buffers and `abi.encodePacked` of unsigned/address/bool/bytes32 scalars and admitted byte buffers. Packed buffers preserve exact byte widths and lengths using aligned word memory; nested buffers receive separate allocations. Hex numeric literals retain their exact value. Dynamic byte parameters, arbitrary byte locals, direct packed structs, signed/fixed-byte widths other than bytes32 and effectful scalar arguments remain rejected. The focused 96-case A/B/C campaign includes an imported library key derivation over a complete dynamic root (`RecordHashLib.toKey`, byte-pinned in `imported-types/manifest.json`), storage/events and rollback. All four generated variants agree, 15 semantic mutants are detected with minimized witnesses, and 11 located rejection/acceptance controls pass on captured local snapshots. Copy-loop and packed-allocation helper proofs are in `AbiMemory`; exact-head release gates remain pending. |
| Internal struct reference arguments | Root memory-to-memory and calldata-to-calldata references retain the exact ABI descriptor and nominal struct declaration identity across acyclic single-return helpers, including internal library receivers. External reference helper calls and raw Yul pointer access reject. Static and dynamic roots preserve eager memory/lazy calldata validation. Cross-location copies, storage references and unsupported reference expressions reject with source locations. Twenty A/B/C cases across four equivalent variants and a wrong-root mutation cover this rule; located rejection mutations cover external-call boundaries, location conversions and Yul name shadowing. |
| Single assignment to a named assembly return | `xor`, `mul`, `lt`, as in `UtilsLib.min` |

Non-empty roots with unnamed return parameters must return explicitly on every non-reverting path. Payable roots are rejected until value-transfer
semantics are supported. Other `msg`, `block`, and `tx` context members are
rejected when reached. Loops, mapping-to-struct writes, compound assignments, external calls
(other than the typed-interface staticcall, checked-template `create2`, optional-bool
low-level `.call` and `<address>.code` rows above),
external library calls (a `public` or `external` library function called from
outside its library, directly or through `using for`: solc emits a
`DELEGATECALL` to the library linked at deployment, whose code the source does
not determine; internal library functions, and public ones called by name
inside their own library, are inlined),
modifiers, recursion, named call arguments, signed
operations, and any other construct reached from a root are rejected with
`file:line:column`, the construct, the reason, and the call path from the root
(`closure: C.f -> L.unused`). Functions outside the closure are listed as
excluded and do not block the import. Only reached storage fields are decoded;
array/mapping struct members are reported as opaque and cannot be read.

## What each check establishes

Four questions are answered separately, per root; none implies the next.

1. **Importable.** The command succeeds, or fails with the diagnostic above.
   A partial model is never produced, so every listed root is importable.
2. **Runs on Denote** (`denoteCovered`). Every constructor in the body has an
   explicit denotation arm (not the catch-all). The kernel proof for all roots
   together is `x.covered`.
3. **Compiles** (`compilable`). The ordinary Verity compiler accepts the root on
   its own. This is a compile attempt, not a correctness result; agreement
   with Denote and solc is only sampled by the A/B/C campaigns below.
4. **Covered by compiler proofs** (`compilerProofCovered`). Always
   `unavailable`: the importer builds no `SupportedSpec` witness and
   `SupportedSpec` has no decision procedure. The report never implies it.

`x.report` records 1, 2 and 4 (`status` lines of `toText`). Compilation depends
on the compiler, not the import, so the differential driver reports all four:

```lean
#eval IO.print (Differential.statusText x.model x.report)
```

```text
function f
  importable true
  denoteCovered true
  compilable true
  compilerProofCovered unavailable (the importer builds no SupportedSpec witness; compiled code is only tested by A/B/C)
```

## Trust boundary

solc's AST and storage layout, and the lowering in `Import.lean`, are trusted.
Inlined helper bodies are the code solc compiles into the contract. Code that
runs behind a `DELEGATECALL` to a linked library is chosen at deployment and is
never inlined (`check_library_call_rejections`).
The model is built as ordinary values and quoted (`Quote.lean`); after
elaboration the definitions are evaluated back and must equal those values.
The digest is SHA-256 over framed JSON of the complete solc input, the selected
signatures, the solc release, and the sources of `Import.lean`,
`Coverage.lean`, `Report.lean`, `Quote.lean` and `Profile.lean`. The statement
denotation retains exact panic bytes; legacy scalar accessors erase failure
bytes. Gas, public ABI decoding and bytecode equivalence remain outside the
import certificate.

Consumers should re-elaborate in CI, check the fresh model is `rfl`-equal to
the compiled import, and keep a reviewed inventory (`report.toText`) and a
golden `repr` of the model, as the pilot's `check_import.py` does.

## Differential validation

Tests supplement proofs; no test count establishes equivalence. Every case
runs three paths:

- **A:** the original Solidity, compiled by the pinned solc, run in Foundry.
- **B:** the imported model, run by `Denote.execStmtList` (the proofs'
  semantics) with Verity's pure Keccak for mapping slots.
- **C:** the model compiled by Verity to Yul, then by solc, run in Foundry.

A consumer supplies a JSON fixture (see
`Contracts/SolidityImportSmoke/differential.json`): source and signature,
input domains, argument projections, storage recipes and a fixed corpus.
Python builds calldata with `eth-abi` and storage slots with `eth-hash`,
independently of Verity. Unused packed bits, neighbouring words and unrelated
slots get noise. Each EVM case runs from a restored snapshot and must not
write storage.

A/B/C must agree on success/revert, return words, observed storage, and exact
return/revert bytes. A payload-free Denote failure is a harness error. Timeouts, resource limits, unsupported
compilation and tool failures are harness errors, never reverts.

```sh
scripts/check_solidity_differential.sh --config Contracts/SolidityImportSmoke/differential.json \
  --output .lake/d/smoke --seed 2438 --cases 128        # inputs
scripts/check_solidity_differential.sh --programs 5 --cases 16 --seed 2438 --jobs 4 \
  --output .lake/d/programs                             # generated programs
scripts/check_solidity_differential.sh --mutations --output .lake/d/mutants
scripts/check_solidity_differential.sh --replay --output .lake/d/smoke
scripts/check_solidity_differential.sh --reduce --reduce-seconds 120 --output .lake/d/failing
```

- **Generated programs** cover uint8/16/128/248/256 casts, checked arithmetic,
  ternaries and helpers. Each also runs renamed and helper-extracted variants
  that must behave identically (`metamorphic-divergence.json` on mismatch).
- **Replay and reduction.** A campaign records seeds, inputs, sources, solc
  input/output, Yul, bytecodes, tool versions and hashes. Replay refuses
  changed artifacts. The reducer shrinks inputs (and generated expression
  trees) while preserving the mismatch category.
- **Mutants** are real importer and Denote edits built in isolated copies.
  The unchanged copy must first pass A/B/C on the same fixture and inputs;
  an existing divergence cannot count as a detected mutation.
  Each must produce a runtime divergence; one that fails to compile is
  invalid, not detected.
- **Importer regressions:** `python3 scripts/solidity_import_mutations.py`
  checks the golden model (`--update-golden` after review), hygiene,
  determinism, rejections with diagnostics, multi-root independence, and that
  source changes move the witness results and the digest.
  `--shard I/N --jobs J` runs a deterministic share of the independent
  campaigns with `J` parallel isolated snapshots (`--jobs auto` sizes `J` by
  cores and available memory; `--task NAME` selects single campaigns); CI's
  `import-mutations` job runs six shards from the prepared `build` workspace.

CI runs fixed seeds on every PR (10 minutes) and longer input, program and
mutant campaigns nightly and on demand (60 minutes), archiving the evidence.
A timeout fails the job.

## Adding a construct

A new construct needs, in the same PR: positive, rejection, boundary and
interaction cases; an A/B/C fixture or generated-program coverage; a mutant
when it carries real risk; and the Lean proofs it enables. Keep the smoke
golden model and the Midnight proofs green, and turn every reduced
counterexample into a permanent regression.

EVMYulLean has a bytecode executor (`EvmYul.EVM.Ξ`) that could become a fourth
path; it would need account/block setup, opcode conformance checks and
independent result decoding, and must not replace Foundry.

## Pinned-corpus import coverage

`python3 scripts/solidity_import_coverage.py --fetch` checks the immutable
corpus in `scripts/solidity_import_corpus/manifest.json`: Midnight, Uniswap
v2/v3 core contracts, Pareto credit vaults, and OpenZeppelin ERC20/ERC4626.
`--fetch` permits downloading pinned source commits and checksum-verified
inventory compilers and dependency archives. No npm lifecycle scripts run.
Subsequent runs can omit it. Artifacts go to `.lake/solidity-import-coverage`;
CI publishes JSON, Markdown, per-function import logs, and the inventory
compiler input/output without making coverage a build gate.

The current denominator is **implemented functions in the selected
contract and its solc C3 inheritance chain**, including internal/private helpers.
Most-derived implementations win by signature; private helpers retain their
declaring-contract identity. Constructors, generated getters and abstract
declarations are excluded. Inherited implementation selection failures are
reported against the declaration that the importer cannot select. Each probe
checks the root's declaring contract in the import report, so a same-named
private helper cannot stand in for an inherited implementation.
Fallback/receive bodies remain counted and are rejected as unnamed roots.
A project may list optional `"exclude_functions"` (function names) in the
manifest; it is then reported both in full and as a milestone with only those
functions removed (Midnight currently excludes `multicall`). This is function-import coverage, not whole-contract ABI or EVM
coverage. Historical reports made before removal of scalar struct projections
may count projected imports; rerun the instrument on the current importer
before using those reports to assess complete ABI support.

Inventory uses the source project's pinned solc, preserving its original
pragmas. Each named declaration then goes through the actual Lean importer
under its current compiler pin. Source-version mismatches are reported as
pragma blockers, never fixed by rewriting sources. A successful probe requires
both a zero process status and the post-import marker. Timeouts, crashes,
unlocated importer errors, missing dependencies, and kernel errors are unknown
measurements. Unknown functions stay in the denominator; an unavailable
contract inventory suppresses the aggregate percentage. Reports explicitly
mark incomplete measurements and pending contracts. Fresh incomplete artifacts
replace prior-run output before the build starts; a timeout cannot leave an
old success report behind. The CLI returns nonzero for incomplete measurements,
which CI treats as advisory.

The first-blocker histogram weights each diagnostic by the number of rejected
functions encountering it first. These are **potential** unlocks, not a promise
that implementing that construct alone makes all those functions importable.
Rerun the report after each lowering family to reveal subsequent blockers.
The report records implementation hashes; source changes during measurement
invalidate that contract's results.
Legacy compiler-version blockers must be addressed before their construct
histograms can be compared with Midnight's. No coverage result is a proof of
semantic equivalence; that requires the separate differential/proof evidence.

The initial corpus campaign exposed uninitialized-local rejections that lacked
Solidity source locations. These remain unsupported, but now fail at the
`VariableDeclarationStatement` with a precise diagnostic instead of a missing
JSON-field error. This diagnostic correction does not change successful models
or the smoke golden; the importer source digest changes as designed.



### Imported transaction-context sequences

`EnvironmentSequence.sol` is an actual three-entry-point import.
`solidity_differential.check_environment` generates direct, local-binding, and
internal-helper variants in `programs.py`, imports each generated source into
Denote and the Verity compiler, and compares all three execution routes. It also
compares transaction inputs and complete observations between variants. Sender,
contract address, timestamp, block number, and chain id are checked through their
ABI return bytes across three funded callers. This fixture exercises context and dispatch; it does not
establish storage-write or external-call import support.

The executable context mutations replace each new imported context expression
with zero. Every mutant must first pass the unchanged fixture, then produce a
real A/B/C divergence and a separately replayed, deletion-minimal one-transaction
witness. Tool and compilation failures cannot count as detection.

### Imported scalar storage sequences

`StorageSequence.sol` imports three mutating entry points with packed uint128
siblings, a packed address/uint96 pair, and a full uint256 field. Transactions
exercise successive writes, deletion of one sibling while retaining the other,
and writes followed by a message-bearing revert. Direct, local-binding, and
reordered-write variants are independently imported and run through A/B/C.
Cross-variant comparison treats storage as a key/value map and touched slots as
a set; it preserves ordered events, status, and exact return/revert bytes and
rejects duplicated or missing storage observations.

The physical model fields are uint256 words with solc-derived bit ranges;
Solidity source types still control conversions and return ABI types. Boolean,
signed, array, and direct struct storage are rejected in this slice. Storage
assignments are accepted only as root statements. Helpers that write storage
are rejected until nested operand and argument evaluation order is validated. Mapping
writes and whole-contract deployment/initialization are not established by this
fixture. The importer still selects runtime function closures.

Write-aware executable coverage is separate from the original read-only
`stmtCovered` predicate and its world-preservation theorem. Storage frame lemmas
in `StorageFrames.lean` prove preservation of other persistent slots for the
actual Denote write helper and successful `setStorage` step, including packed
writes and normalized alias destinations. They do not by themselves prove a
whole-contract invariant or preservation of other bits in the same slot.

`EntryPointInvariants.lean` supplies `AllEntryPointsPreserve` obligations for
every public function in a model. Proving these obligations lifts an invariant
to arbitrary finite `EntryPointSequence`s. `ContextualEntryPointSequence`
additionally requires that environment preparation preserve the invariant.
The execution uses `Denote.effectiveFields`, including namespaced fields, and
the model's custom errors. Reverting frames restore the transaction's initial
world; `all_entry_points_preserve_of_success` therefore reduces the obligations
to successful calls and preservation by the frame reset.

`EntryPointInvariantChecks.lean` proves that a stored word stays at most one
across every sequence of three public entries: write zero, write one, and
write 99 followed by panic and rollback. This handwritten model illustrates
the proof interface; it does not establish an invariant for Midnight. ABI
decoding, dispatch, value transfer, and initialization remain separate
obligations, as do loop reasoning and external reentrant transitions.

`StorageVoidSequence` checks empty ABI responses and rollback from void entry
points. Its fallthrough lowers to `Stmt.stop`; the compiler's return-shape
validation remains unchanged. `StorageBytesSequence` separately checks bytes32
assignment, read, deletion, and rollback. Both have direct, binding, and
arithmetic-identity variants generated in `programs.py`.

### Imported scalar mapping sequences

`MappingSequence.sol` exercises one-key uint128 and bytes32 mappings, two-key
boolean authorization and uint128 consumption mappings, rollback, deletion,
and distinct transaction senders. Direct, local-binding and reordered-write
variants are imported independently and compared through the three stateful
routes. Mapping values are represented as a synthetic single member at word
zero, with solc-derived width; narrow writes retain the remaining word bits.
Boolean reads normalize the loaded byte to zero or one. No Solidity struct
member access is exposed by this internal representation.

Mapping slot observations evaluate keys in the current Denote state and use
the supplied Keccak oracle, including both hashes for nested mappings. Reached
key/value reads and writes before rollback remain observable.
Signed and unsigned integer mapping keys are supported; dynamic key types and
unsupported value encodings remain rejected with source locations. Numeric literals
with supported denominations use the exact integral lowering described above; nonintegral
results and string literals used as numbers are rejected explicitly.

`SignedMappingKeysSequence.sol` checks signed mapping keys at 8, 64, 128, and
256 bits against source and compiled-model execution. Fixed inputs cover zero,
negative one, signed minima/maxima, narrowing aliases, and rollback. The same
fixture covers packed and raw-slot signed member reads, signed bounds, and signed
ABI arguments. Narrow signed reads sign-extend the extracted storage bits before
widening or comparison. The signed-key/member elaboration controls admit these
supported layouts; unsupported key encodings still reject.

`YulFeeContextChecks.lean` exercises `basefee()` and `gasprice()` with distinct
nonzero values and wrapping arithmetic boundaries, and checks compilation. The
Yul arity validator admits both zero-argument builtins.

The mapping dirty-slot campaign seeds identical independently hashed slots in all
three routes. Its fixed prefix reads a noncanonical true byte, deletes it while
preserving upper bits, then reads the zero low byte with those upper bits still
set. Narrow assignments, deletes, rollback and later reads compare complete
words, including bits outside the declared value width.

Imported event sequence fixtures exercise indexed/unindexed scalar words,
empty and repeated events, and rollback of emitted events. The narrow fixture
uses a matching `uint128` parameter; widening a different parameter or passing
a local narrow value remains a located rejection under the compiler's existing
narrow event check. Generated renamed/binding/order variants preserve the exact
ordered event sequence. `--argument-bits` generates canonical narrow ABI words;
it does not claim malformed-calldata equivalence.

### Bounded-loop proof rule

`Compiler/SolidityImport/LoopInvariants.lean` proves an indexed-invariant rule
for Denote's actual `execForEachLoop`, and lifts it to `.forEach` after successful
count evaluation. The step obligation includes the normalized index binding;
the initial obligation includes the binding installed even when the bound is
zero. Normal completion establishes the invariant at the final index. Stop,
return, unclassified revert and byte-carrying revert have a separate explicit
postcondition, retaining their complete outcomes.

`LoopInvariantChecks.lean` applies the rule to a storage-writing loop for any
evaluated bound, and proves exact propagation of panic bytes on the first
iteration. This is model proof infrastructure: it adds no Solidity lowering
and does not establish a source-loop correspondence, gas bound, reentrancy
property or invariant of Midnight.

### Bounded symbolic execution

`Compiler/SolidityImport/SymbolicExecution.lean` composes already-established
Denote transitions. `denote_step using h` consumes one continuing statement;
`denote_prefix using h` composes an explicitly delimited prefix. Each uses the
provided equality proof and preserves the complete state. Neither tactic
unfolds expression evaluation or asks the kernel to reduce a whole imported
body. If the supplied theorem does not describe a matching continuing step,
the tactic fails rather than silently skipping it.

The terminal composition rule retains the entire outcome: final state for stop
or return, and exact byte list for a byte-carrying revert. The suffix is then
unreachable. These rules extend the generic list-composition lemmas ported
from the pinned Midnight pilot; they do not prove Solidity/model equivalence
or discharge the semantic obligations of an instruction. For loops, use the
indexed rule above to establish a bounded block theorem before composing it.

The check module exercises arbitrary-state step/prefix composition, early stop,
exact revert bytes, rejection of an incompatible step proof, and a concrete
bind-then-stop sequence whose unreachable suffix is arbitrary.

### Development slice: loops in inlined helpers

A shared loop lowering draft reuses the exact unsigned zero-start/unit-step/invariant-bound checks for root entry points and helpers. Helper loop bodies admit supported scalar locals, assignments/deletion, requires, events, conditionals and nested loops. A helper's final result resumes its caller; returns inside its loop body remain precisely rejected. `HelperLoopSequence` checks the caller continuation.

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Invariant bounded `for` in an internal scalar-result helper | Shared counter/bound/header checks; helper body has no return; unsupported effects fail with source diagnostics |

No release validation or Midnight coverage improvement is claimed for this draft.

### Development slice: unsigned mapping-struct member writes

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Assignment and `delete` of unsigned members in one/two-key mapping structs | Existing exact layout word offsets and packed masks; opaque/unsupported members reject; direct key preludes reject |
| Storage aliases with mutable local keys | Keys are captured into fresh bindings at declaration, including the outer key of a nested mapping |

`PackedMemberWriteSequence` exercises sibling fields, packed widths, full words, alias key changes, deletion, events and rollback. No native validation or Midnight coverage improvement is claimed yet.

### Development slice: internal helper expression effects

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Scalar/local/mapping/unsigned mapping-struct assignments and `delete` in scalar-result helpers | Reuse the exact root effect rules and rejection diagnostics; execute effects before the helper continuation |

`HelperEffectSequence` checks writes, packed siblings, conditional effects, deletion, caller continuation and rollback. Compound operations, parameter writes, unsupported reference targets and external expression calls remain rejected. This draft has not passed native validation or full release gates.

The current revision also guards stateful helper calls inside ordinary binary operands and helper call arguments until their evaluation order is independently validated. Non-view declarations are conservatively classified as stateful. Short-circuit boolean branches retain their existing selected-branch evaluation; the fixture checks that a dead helper cannot write. These guards and the expanded fixture are development changes awaiting compilation and mutation controls.


### Development slice: fixed arrays behind mappings

| Supported Solidity (development; full release validation pending) | Lowering boundary |
| --- | --- |
| One-dimensional fixed unsigned arrays behind one/two-key mappings | Validate fixed length, unsigned base layout and exact rounded footprint; use floor(256/width) elements per slot and masked element writes/deletes |
| Dynamic unsigned indices into those arrays | Capture the index once, select the resolved element and emit exact panic 0x32 for an out-of-range index |
| Readonly storage-to-memory copies of those fixed arrays | Capture all elements at declaration; scoped descriptors preserve the snapshot across subsequent storage writes |

Effectful or reverting write keys, indices and RHS operands reject until their
evaluation order has dedicated validation. Dynamic/multidimensional/signed/bool
arrays, memory writes/aliases and whole-array values remain outside this slice.
Two preliminary 64-transaction A/B/C campaigns passed on recorded source hashes;
the second covered indices 0–8, snapshot identity, uint24 cross-word packing,
delete, two mapping keys and rollback. New exact-head variants, rejection and
mutation controls and full release gates are still pending.

The fixed mapping-array key/index order audit passed 32 actual A/B/C transactions
on `2a448958`: two state-changing helpers produced stamp12 on success, invalid
indices produced panic0x32, and competing helper failures produced the exact
`first array key` revert bytes. This establishes that fixture under the pinned
compiler settings; it is not a general Solidity evaluation-order theorem.


### Development slice: fixed-array assignment evaluation order

| Supported Solidity | Exact lowering |
| --- | --- |
| Checked/effectful RHS and key/index expressions of mapped fixed-array assignments | Evaluate and capture the RHS, then the mapping keys and index in recursive source order, then bounds-check and perform the masked write. Existing expression rejection boundaries remain in force. |

The pinned solc 0.8.34 via-IR/Osaka/466-runs A-only audit at `3bc74c208`
observed the stamp `312` for RHS/key/index helpers and RHS error priority over
bounds and key errors. This is evidence for that fixture/profile, not a general
Solidity evaluation-order theorem. `FixedArrayWriteOrderSequence` extends the
A/B/C obligations to distinct key/index/RHS failures, checked division and
narrowing, emitted events, bounds and rollback; baseline, identifier-renamed
and explicitly captured-RHS variants must have identical observations. Two
runtime mutations exchange RHS/LHS order or corrupt the captured RHS. These
new A/B/C campaigns and full exact-head gates are **pending**; no additional
Midnight importability is claimed yet. The prior three key/index/RHS rejection
controls become positive controls for the newly admitted forms; compound and
dynamic writes and unresolved stateful binary-operand order remain rejected.


### Development slice: discarded scalar helper calls

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Internal/private scalar-result helper calls used as expression statements, including library calls | Keep the helper prelude, materialize the final result even when unused, then resume the caller; retain recursion, dispatch, argument-order and reference-conversion guards |

The fixture checks helper storage writes, events, early return, caller continuation,
library reverts and rollback. Void/multiple-result helpers and calls to external
or public declarations remain precisely rejected in this statement slice. This
prerequisite does not implement CREATE2 code-deployment helpers: named returns, dynamic
byte construction and CREATE2 still require independent exact lowering and observations.
Generated variants and an effect-drop runtime mutant are registered; native and
full release checks remain pending. Existing Denote instructions are reused.

Helper-result continuations also reuse the exact root `emit` lowering, keeping events
before the continuation and rollback intact. The fixture retains helper events;
a separate event-drop runtime mutation and anonymous/dynamic event rejection
controls are registered. Native validation remains pending.

### Development slice: encoded byte locals

| Supported Solidity (development; complete validation pending) | Lowering boundary |
| --- | --- |
| Initialized `bytes memory` locals from admitted ABI/packed encodings or literals; local aliases | Evaluate encoding once at declaration and retain a payload pointer and logical length. Hashing and packed concatenation consume those captured descriptors; branch/helper/root scope restoration preserves declaration identity. |

The initial draft fixture passes 64 real A/B/C transactions with repeated reads,
aliases, nested buffers, branch locals, storage/events and rollback. Generated
variants, three runtime mutations and nine located controls are added but await
native validation on the final commit. Byte assignment/index writes, length
access, `new bytes`, byte parameters/helper reference calls, raw Yul pointers and
deployment remain unsupported and rejected. The descriptor is a payload view,
not a claim of general Solidity byte-object memory layout. Full exact-head release
gates remain pending.

### Development slice: named scalar helper results

| Supported Solidity (development; native validation pending) | Lowering boundary |
| --- | --- |
| Named unsigned/address/bool/bytes32 result in a single-result internal helper | Initialize a declaration-bound result to zero, preserve assignments and early explicit returns, and return its value on fallthrough. Restore result context across nested helper calls. |
| Existing single Yul assignment followed by a helper continuation | Assign the named result only when `InlineAssembly.externalReferences` resolves the target identifier to the active helper return declaration (`!isOffset`, `!isSlot`, no suffix, `valueSize == 1`), then continue with the following statements. Clean narrow unsigned/address results by masking and booleans by nonzero normalization. Assembly assignments in branches retain the caller continuation. |

A structural direct-result path retains existing full-word single-terminal-assembly
models. This adds no Yul builtin, deployment or external-call semantics. Yul reads
of narrow named results are rejected because the current result slot stores a
clean Solidity value, whereas Yul could observe dirty bits. Shadowed local
targets with the same name as the helper return reject at the Yul assignment;
reference locals (`bytes memory`, fixed memory array snapshots and storage
aliases) erase shadowed names from Yul identifier lookup within their lexical
scope. Reference/tuple results, modifiers, recursive calls and statements after
an explicit return remain rejected. Bare returns are rejected, matching the
pinned solc source audit; implicit named-result fallthrough is supported.

The initial draft passed 93 build jobs and 64 A/B/C transactions. The expanded
fixture adds nested contexts, boolean/address cleanup, assembly branch
continuation and lexical shadowing. Three generated variants, runtime and guard
mutants and sixteen located controls await native validation on the final commit.
Full release gates and the pinned pilot check remain pending; no golden or
provenance was changed.

### Development slice: numeric Yul expressions

| Solidity construct | Lowering |
| --- | --- |
| Untyped decimal or hexadecimal Yul numeric literal fitting one EVM word | Parse the exact natural value and reject values outside `[0, 2^256)`. |
| Two-argument Yul `add` in the existing single-assignment helper subset | Use the existing wrapping word addition expression. |

This draft reuses existing literal and addition semantics in Denote and codegen.
It does not expose byte-buffer pointers or add raw memory, deployment, additional
assembly statements, typed literals or nonnumeric literals. These remain precise
rejections. `YulNumericSequence` exercises decimal, hex and full-word literals,
overflow, storage, events and rollback. Baseline, identifier-renamed and numeric
normalization/commuted-add variants are generated; runtime literal/add mutations
and located acceptance/rejection controls are registered. Native validation,
exact-head release gates and the pinned pilot check are pending. This is a
prerequisite for CREATE2 key-derivation helpers, not an implementation of code deployment.

### Development slice: pinned `solc 0.8.10` release and single-quoted imports

| Supported profile / source form | Lowering and provenance boundary |
| --- | --- |
| `Profile.solc := "0.8.10+commit.fc410830"` | Verified against `.lake/solidity-import/solc-0.8.10` SHA-256 pins (Linux and macOS) before and after invocation; requires `viaIR := false` and `evmVersion` up to `"london"`. |
| Single-quoted and double-quoted `import` paths | `importSpecs` extracts both `'...'` and `"..."` import specifiers; after compilation, every key in `parsed["sources"]` must belong to the explicitly collected `sources` map so `solc 0.8.10` cannot silently load uncollected host files without `--no-import-callback`. |

### Development slice: C3 inheritance, virtual helper dispatch, and `super` / base-qualified calls

| Supported Solidity | Lowering boundary |
| --- | --- |
| Inherited root entry points across `linearizedBaseContracts` | `selectFunction` walks the target contract's C3 `linearizedBaseContracts` in most-derived-first order, preferring implemented declarations over unimplemented interface/abstract declarations in the same virtual override family (`baseFunctions` transitive closure) or parameter signature, and switches `currentFile` to the declaring file of the selected root. |
| Unqualified internal/private helper calls in base contracts | When the referenced function's enclosing contract belongs to the target contract's `linearizedBaseContracts`, `lowerCall` resolves the call to the first implemented override in the target contract's C3 chain sharing the same transitive `baseFunctions` family, and restores `currentFile` across inlined helper frames. |
| `super.fn(...)` helper calls | Verified against `referencedDeclaration == -25` (`type(contract super ...)`); resolved to the first implemented function in the same transitive `baseFunctions` family across the suffix of the target contract's `linearizedBaseContracts` strictly after the calling function's enclosing contract (matching `solc` C3 diamond `super` dispatch). |
| Explicit base-qualified `Base.fn(...)` helper calls | Verified that `Base` is an identifier in the target contract's `linearizedBaseContracts` and that `fn` is declared in `Base`, then inlined statically without virtual dispatch. |
| Duplicate `storageLayout` labels (e.g. OpenZeppelin `private __gap`) | Unreferenced duplicate labels in `storageLayout.storage` do not block importing supported functions; any reference to a state variable whose label appears multiple times in `storageLayout.storage` fails closed with `shadowed storage declaration <name> is outside this slice`. |

### Development slice: void helpers, custom-error reverts, scalar booleans, and named root returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Zero-return internal, private, and internally-called public helpers | Lowered via continuation-passing (`lowerVoidHelperFrom`) so nested early `return;` inside `if`/`else` runs the post-conditional continuation only on fallthrough paths with restored lexical scope. |
| `revert CustomError(...)` (`RevertStatement`) | Lowered through `lowerErrorArguments` to `Stmt.requireError (.literal 0) name values`. |
| Scalar `bool` storage variables and prefix `!` | Stored as 8-bit packed storage with `logicalNot (logicalNot ...)` normalization on read and write; prefix `!` on `bool` lowers to `Expr.logicalNot`. |
| Named scalar root return parameters and empty-body scalar hooks | Root functions whose return parameters are all named scalars initialize each to zero and return them on bare `return;` or fallthrough; empty-body root or helper hooks return zero words. |

### Development slice: pre-placeholder modifiers, `unchecked` blocks, compound assignments, and scalar assignment expressions

| Supported Solidity | Lowering boundary |
| --- | --- |
| Pre-placeholder modifiers (`ModifierDefinition` / `ModifierInvocation`) | Modifiers whose body ends with a single trailing `_;` (`PlaceholderStatement`) and contains no earlier `_;`, no `return;`, and no `virtual` specifier are inlined in declaration order before root and helper bodies with their own lexical frame and `unchecked := false`. |
| `unchecked { ... }` (`UncheckedBlock`) | Enables wrapping unsigned arithmetic (`+`, `-`, `*` masked to `2 ^ bits - 1` when `bits < 256`) within the lexical block while preserving division/modulo-by-zero panic (`0x12`) and resetting `unchecked := false` across helper and modifier call boundaries. |
| Compound assignments (`+=`, `-=`) | Supported on declaration-bound unsigned scalar locals, unsigned scalar storage fields, unsigned scalar mappings, and unsigned mapping struct members, honoring checked vs `unchecked` arithmetic. |
| Scalar assignment expressions (`(x = rhs)`) and constant `**` | Supported for `=` on declaration-bound scalar locals and scalar storage identifiers when any binary sibling operand is order-independent (`Literal` or constant) and call sites are single-argument; integer constant `a ** b` lowers when `a ^ b < 2 ^ 256`. |

### Development slice: multi-return helper inlining, tuple destructuring, parameter compound assignments, and narrow constant event arguments

| Supported Solidity | Lowering boundary |
| --- | --- |
| Multi-return internal, private, and internally-called public helpers | Unnamed multi-return scalar helpers (`returnParameters.parameters.size > 1`) allocate fresh `letVar` result bindings initialized to zero, evaluate and convert `Return` tuple components in source order into those bindings, and thread post-`if`/`else` continuations along fallthrough paths via `lowerVoidHelperFrom`. Named or reference return parameters and discarded multi-return calls remain rejected. |
| Tuple destructuring declarations and assignments (`(uint256 a, uint128 b) = fn(...)`, `(a, b) = fn(...)`, `(uint256 a, , uint128 c) = (x, y, z)`) | Supported when the RHS is a multi-return helper call of matching arity, or, for declarations only, a literal `TupleExpression` of matching arity whose components are evaluated left to right (including elided ones, so their panics and reverts keep solc's order) through the conditional-tuple leaf lowering before the fresh locals are bound; `VariableDeclarationStatement` requires at least one non-null declaration and binds declared components in order; `Assignment` (`=`) evaluates converted components into fresh temporaries and commits each non-elided target to a materialized scalar local or scalar storage field in order after rejecting duplicate local or storage targets. |
| Compound assignments (`+=`, `-=`) on unsigned scalar parameters | When an unsigned scalar parameter is modified by `+=` or `-=` in a root, helper, or modifier body (without direct `=` or `delete` parameter writes), the parameter is materialized into a declaration-bound mutable local copy at frame entry so call-by-value updates are visible within the frame without mutating caller bindings. |
| Narrow constant event arguments (e.g. `emit Initialized(type(uint8).max)`) | Canonical integer literals `Expr.literal n` with `n < 2 ^ bits` and empty prelude are accepted for `.uintN bits` event parameters in both `Import.lean` and `ValidationEvents.lean`, alongside direct matching `.uintN bits` parameters. |

### Development slice: `int256` arithmetic/storage/mappings and contract-typed scalar values

| Supported Solidity | Lowering boundary |
| --- | --- |
| `int256` / `int` scalar parameters, locals, returns, scalar storage fields, and scalar mapping values | Lowered as full 256-bit two's-complement words (`ParamType.int256` and `Word Int256` accessor bridge); narrow signed (`int8`..`int248`) locals and arithmetic keep sign-extended words (`signextend`), exercised for `%` by `SignedModuloSequence`; signed integer mapping keys are supported, including the narrow-key checks described above. |
| `int256` prefix unary `-`, binary `+`, `-`, `*`, `/`, `%`, `<`, `>`, `<=`, `>=`, `==`, `!=`, and `+=` / `-=` / `%=` | Checked `+`, `-`, `*`, `/`, and unary `-` emit `Panic(0x11)` on two's-complement `int256` overflow (including `-type(int256).min`, `type(int256).min * -1`, and `type(int256).min / -1`) and `Panic(0x12)` on division by zero; `UncheckedBlock` switches signed `+`, `-`, `*`, `/`, `+=`, `-=`, and unary `-` to wrapping 256-bit two's-complement arithmetic while preserving division-by-zero `Panic(0x12)`. Signed comparisons use `slt` / `sgt` and signed division uses `sdiv`. Signed `%` and `%=` (`signedModulo`) use `smod`, the truncated remainder with the sign of the dividend (`(-7) % 4 == -3`, `7 % -4 == 3`), after the `Panic(0x12)` zero-divisor guard, which `UncheckedBlock` keeps; `type(int256).min % -1` is `0` and never panics. `SignedModuloSequence` (fixture `signed-modulo`) runs three equivalent variants A/B/C, the third rewriting every `a % b` except `min % -1` as `a - (a / b) * b`. |
| `type(int256).max`, `type(int256).min`, `type(uintN).min`, and `int256(x)` / `uint256(int256_x)` casts | `type(int256).max` lowers to `2^255 - 1`, `type(int256).min` to `2^255` (`-2^255` in two's complement), and `type(uintN).min` to `0`; explicit `int256(...)` and `uint256(...)` casts on 256-bit scalars and bounded constants preserve the 256-bit word representation. |
| Contract and interface scalar values (`contract Foo`, `address payable`) | Supported as 160-bit address-backed scalar parameters, locals, returns, scalar storage fields, scalar mapping values, and `ContractOrInterface(addr)` / `address(contractVal)` casts; external contract member calls fail closed with located diagnostics. |

### Development slice: internal function-pointer locals, mapping-struct `delete`, and post-placeholder modifiers

| Supported Solidity | Lowering boundary |
| --- | --- |
| Internal function-pointer local declarations (`function(...) internal ... ptr = f` or `cond ? f : g`) | Supported when initialized at declaration time to a direct internal/private helper identifier or a `Conditional` (`cond ? f : g`) whose branches resolve to internal/private helpers in the active contract hierarchy. For a conditional initializer, the condition is evaluated once at declaration and stored in a fresh boolean local; calling `ptr(args)` lowers to `lowerCall` on a direct target or a conditional dispatch evaluating arguments once in caller source order and branching on the stored condition to inline each target helper. Reassignment, uninitialized function-pointer locals, function-pointer parameters/returns/storage, and external function pointers fail closed with located diagnostics. |
| Whole-struct `delete` on mapping-backed structs (`delete m[k]`, `delete m[k1][k2]`) | Supported when the referenced struct has no `opaque` (nested mapping or dynamic array) members in `storageLayout` and every decoded member is an unpacked or packed scalar (`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`). Keys are evaluated once into fresh temporaries if needed and each member is cleared to `0` in layout order. Structs with `opaque` or array members fail closed. |
| Modifiers with statements after `_;` (`ModifierDefinition` / `ModifierInvocation`) | Modifiers with a single top-level `_;` (`PlaceholderStatement`) may include both pre-placeholder and post-placeholder statements (for example `nonReentrant` guards). Multiple modifiers wrap outside-in around the body (`m1` outer, `m2` inner). On every non-reverting return or fallthrough path, return values are captured into fresh temporaries before running post-placeholder statements in the modifier's lexical frame. Modifiers with zero, multiple, or nested `_;` placeholders, `virtual` modifiers, and `return;` inside a modifier body fail closed. |

### Development slice: empty-body dynamic array returns and root `bytes calldata` parameters

| Supported Solidity | Lowering boundary |
| --- | --- |
| Empty-body root functions returning a single dynamic array (`T[] memory`, named or unnamed) | Supported when `T` is a canonical return array element (`uint256`, `int256`, `address`, `bool`, `bytes32`), the function body has no statements, and the function has no modifiers. Lowers to `Stmt.returnValues [.literal 32, .literal 0]` with `returns := [.array elemTy]` (the 64-byte ABI encoding of an empty dynamic array: offset `0x20`, length `0x00`). Non-empty bodies, modifier-wrapped bodies, or non-canonical element widths returning `T[] memory` fail closed. |
| Root `bytes calldata` parameters (named or unnamed) and `.length` | Supported with `abiDecoding := .explicitPrelude` via `AbiLowering.bytesCalldataHead`, which enforces `solc`'s exact entry checks (`calldatasize >= 4 + 32 * rootHeadWords`, `relOffset <= 2^64 - 1`, `header + 31 <s calldatasize`, `length <= 2^64 - 1`, and `dataOffset + length <= calldatasize`). Unnamed root parameters receive a hygienic identifier so `Param` validation succeeds while preserving the canonical ABI signature. `.length` lowers to the validated `lengthBinding` local; `bytes memory` root parameters, `bytes` locals, and value uses of `bytes calldata` fail closed. |

### Development slice: same-contract overloaded helpers, constant custom-error arguments, conditional tuple expressions, and Yul `tload`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Same-contract overloaded function declarations (`overloadedDeclarations` in `refInt`) | When `solc` records non-empty `overloadedDeclarations` on a function reference, `refInt` accepts the resolved `referencedDeclaration` if every candidate in `overloadedDeclarations` either belongs to the same virtual override family (`sameVirtualFamily`) or shares an origin declaring contract across `baseFunctionClosure` (for example `ERC20._approve(3)` and `ERC20._approve(4)` declared in the same contract). Cross-contract overloads with distinct signatures and no override relationship remain rejected (`ambiguous declaration`), and importing two overloaded roots with the same name in a single slice fails closed (`root function name collision`). |
| Compile-time constant scalar expressions in custom-error arguments (`address(0)`, `type(uintN).max`, named constants) | Alongside decimal literals and direct scalar bindings, `lowerErrorArguments` accepts pure scalar expressions (`numericConstants` identifiers, `typeConversion` casts such as `address(0)`, and `type(T).max`/`min`) whose lowered value has an empty statement prelude (`converted.pre.isEmpty`) and a canonical literal `Expr.literal n` satisfying `Denote.errorScalarValueValid modelType n`. Non-constant or effectful expressions fail closed. |
| Conditional tuple expressions (`cond ? (a0, ..., ak) : (b0, ..., bk)`) | Supported as the RHS of tuple variable declarations (`lowerLocal`) and tuple assignments (`lowerEffect`), including nested `Conditional` branches whose leaves are `TupleExpression`s or multi-return helper calls of matching arity. Target component types are threaded into each leaf so integer constants (such as `0 days`, `1 days`) convert to the declared component type before branch joining via fresh temporaries and `Stmt.ite`. Stateful or assignment expressions inside tuple components fail closed. Literal tuple assignments are admitted and evaluate every right-hand component before updating targets. |
| Transient storage `tload(slot)` in single-assignment `InlineAssembly` | `lowerYul` lowers `tload(a)` to `Expr.tload`, covered by `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses` (evaluating `DenoteState.transientStorage`). `tstore` and multi-statement assembly blocks remain outside this slice. |

### Development slice: fixed-size unsigned scalar array members in mapping structs and root fixed-size array returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Fixed-size unsigned scalar array members inside mapping structs (`struct S { ... uintN[L] arr; }`) | Decoded from `storageLayout` when the array member has `encoding == "inplace"`, `byteOffset == 0`, positive length `L`, and unsigned scalar elements (`uint8`–`uint256`). Expanded on demand (`usedStructFixedArrays`) into packed or full-word `StructMember` entries `__solidity_struct_array_{member}_{index}` at `wordOffset + index / perWord` only in slices that access the array member; unreferenced array members remain listed in `report.opaqueMembers`. Element reads, writes, `delete`, and memory snapshot copies (`uintN[L] memory snap = m[k].arr;`) enforce dynamic bounds checks (`Panic(0x32)`). Whole-struct `delete m[k]` and whole-array `delete m[k].arr` fail closed. |
| Unnamed root fixed-size scalar array returns (`returns (T[L] memory)`) | Supported when a root function declares a single unnamed `T[L] memory` return parameter with supported scalar element type `T` and positive length `L`. Lowered as `L` consecutive ABI return words (`Array.replicate L elemPty`); `Return` statements accept either an inline array literal `[e_0, ..., e_{L-1}]` (converting each pure/stateless component to `T` in order) or a local fixed-size array snapshot identifier of matching type and length. Named `T[L] memory` return parameters, stateful inline array components, and non-snapshot return expressions fail closed. |

### Development slice: `msg.data` / `_msgData()` support and `enum` scalar types

| Supported Solidity | Lowering boundary |
| --- | --- |
| `msg.data.length` and `_msgData().length` | `msg.data` is verified against `referencedDeclaration == -15` and `t_magic_message`; `.length` on `msg.data` or on a zero-argument internal/private/public helper returning `msg.data` (or forwarding another such helper) lowers to `Expr.calldatasize` after running any modifier prelude/postlude on the inlined helper. Multi-statement or parameterized `bytes` helpers fail closed. |
| Zero-parameter root functions returning `msg.data` or `_msgData()` (`returns (bytes memory)` / `returns (bytes calldata)`) | Supported when the root function takes zero parameters and declares a single unnamed `bytes memory` or `bytes calldata` return parameter (`rootMsgDataReturn`). `return msg.data;` or `return _msgData();` lowers to `Stmt.returnValues [.literal 32, .calldatasize, .calldataload (.literal 0)]` with `returns := [.bytes]`, emitting the exact 96-byte ABI encoding of the 4-byte selector calldata (`offset = 32`, `length = calldatasize`, `word0 = calldataload(0)`). Parameterized roots or arbitrary `bytes` return expressions fail closed. |
| `enum` declarations, `Enum.Member`, `type(Enum).min` / `type(Enum).max`, and `Enum` parameters/locals/returns/events/errors | `EnumDefinition`s with `1..256` members are indexed by declaration ID and qualified type name (`enum Contract.Name` / `enum Name`) and lowered as `.uintN 8` scalars. `Enum.Member` lowers to its zero-based ordinal literal, `type(Enum).min` to `0`, and `type(Enum).max` to `members.size - 1`. Root `Enum` parameters emit an entry calldata guard `calldataload(offset) < members.size` that reverts with empty data on out-of-range ordinals (matching `solc` ABI decoding). Uninitialized `Enum` locals default to `0` (first member). Events and custom errors accept `Enum` parameters as `.uintN 8`, including constant `Enum.Member` arguments. |
| Explicit `Enum(x)` and `uintN(enumVal)` casts | `uintN(enumVal)` is a no-op on the underlying 8-bit ordinal; `Enum(x)` from an unsigned integer, `int256`, or integer constant evaluates `x` once and emits a runtime bounds guard (`x < members.size`) that panics with `Panic(0x21)` on out-of-range values. Fallible `Enum(x)` conversions inside `abi.encode` / `abi.encodePacked` arguments and `enum` struct members or storage fields fail closed. |

### Development slice: unsigned exponentiation, bitwise/shift operators, extended compound assignments, and Yul arithmetic/bitwise builtins

| Supported Solidity | Lowering boundary |
| --- | --- |
| Unsigned exponentiation (`**`) in checked and `unchecked` blocks | In `unchecked` blocks, `a ** b` on `uintN` lowers to `Expr.externalCall "exp" [a, b]` (masked to `2^bits - 1` when `bits < 256`). In checked mode, `a ** b` is supported when either the base or the exponent is a canonical integer literal with an empty prelude: a constant base `B >= 2` checks `b <= maxSafeExponent(B, bits)` (`B^maxExp < 2^bits`) and emits `Panic(0x11)` on overflow; a constant exponent `E >= 2` checks `a <= maxSafeBase(E, bits)` (`maxBase^E < 2^bits`) and emits `Panic(0x11)` on overflow; `0 ** b` lowers to `b == 0 ? 1 : 0` and `1 ** b` / `a ** 0` lower to `1` after evaluating the dynamic operand once. Checked exponentiation with both base and exponent dynamic fails closed. |
| Bit shifts (`<<`, `>>`), bitwise binary operators (`&`, `|`, `^`), and unary bitwise negation (`~`) | Constant `int_const` shifts (`a << b`, `a >> b`) fold when non-negative and `< 2^256`. Runtime `a << b` and `a >> b` require an unsigned shift amount `b` and lower to `Expr.shl b a` (masked to `2^bits - 1` for narrow `uintN`), `Expr.shr b a` (unsigned `uintN`), or `Expr.sar b a` (`int256` arithmetic right shift), matching Yul's `(shift, value)` argument order. Binary `&`, `|`, `^` and unary `~` support `uintN`, `int256`, and `bytes32`, masking `~x` to `2^bits - 1` for narrow `uintN`. |
| Extended compound assignments (`<<=`, `>>=`, `&=`, `|=`, `^=`, `/=`, `%=`) | Supported across declaration-bound scalar locals, writable helper/modifier parameters (`bodyCompoundAssignedIds`), scalar storage fields, scalar mappings, and unsigned mapping-struct members: `<<=`, `>>=`, `&=`, `|=`, `^=`, `/=`, `%=` on `uintN`; `/=`, `%=`, `<<=`, `>>=`, `&=`, `|=`, `^=` on `int256`; and `&=`, `|=`, `^=` on `bytes32`. |
| Single-assignment Yul arithmetic, comparison, and bitwise builtins (`sub`, `div`, `mod`, `and`, `or`, `shl`, `shr`, `sar`, `gt`, `eq`, `iszero`, `not`) | Extended `lowerYul` in the single-assignment inline assembly subset (such as `UtilsLib.zeroFloorSub`), lowering directly to the corresponding `Expr` constructors covered by `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses`. |

### Development slice: bounded `while` loops, Yul `clz`, struct local declarations, and `calldata`-to-`memory` struct conversions

| Supported Solidity | Lowering boundary |
| --- | --- |
| Bounded unsigned `while` loops (`WhileStatement`) and `--counter` / `counter -= 1` in `for` loop headers | `lowerWhile` supports `while (v != 0)` / `while (v > 0)` (and `0 != v` / `0 < v`) on a writable unsigned `uintN` local `v` (`bits ≤ 256`) when the body contains no `return`, does not assign `v` before the final statement, and ends with a strictly decreasing bit-clearing or right-shift update: (1) positive constant right shift (`v >>= k` or `v = v >> k`, `1 <= k < 256`), (2) lowest-set-bit clear (`v &= v - 1` or `v = v & (v - 1)`), or (3) MSB bit clear (`uintM b = msb(v); ...; v &= ~(1 << b)` or `v = v.clearBit(b)` where `msb` computes `sub(255, clz(x))` and `b` is not reassigned). Lowered to `Stmt.forEach loopVar (.literal bits) [.ite condVal.expr bodyOut.toList []]`, which executes at most `bits` guarded iterations. `lowerFor` also accepts `--i` and `i -= 1` as `for` loop step expressions so `bodyAssignedIds` detects any counter mutation in loop bodies. |
| Yul `clz(x)` in single-assignment `InlineAssembly` | `lowerYul` lowers `clz(a)` (EIP-7939 Count Leading Zeros, 256 for `0`) into an unrolled 8-step binary search over `[128, 64, 32, 16, 8, 4, 2, 1]` using `Expr.shr` and `Stmt.ite`, producing a pure `Denote`- and `Yul`-compatible statement prelude without requiring custom EVM opcodes in downstream proofs. |
| `memory` and `calldata` struct local declarations (`Struct memory s = ...`, `Struct calldata s = ...`) and `calldata`-to-`memory` helper argument conversions | `lowerLocal` supports non-reassigned `memory` and `calldata` struct locals initialized from a root/helper struct reference (`.mem`) or a struct-array element (`m.tranches[i]`, `.abiElement`). Initializing a `memory` struct local or `memory` helper parameter from a `calldata` struct or `calldata` struct-array element materializes the struct into freshly allocated memory (`AbiRootLowering.materializeFromCalldata` / `AbiRootLowering.materializeElementFromCalldata`), validating scalar bounds and array heads at copy time; `memory`-to-`calldata` conversions and reassigned struct locals fail closed with located diagnostics. Referenced scalar `immutable` state variables require checked deployed bindings (see below). |

### Development slice: `abi.encodeWithSelector`, `.selector` byte buffers, Yul arithmetic/bitwise/context builtins, and external/ABI rejection diagnostics

| Supported Solidity | Lowering boundary |
| --- | --- |
| `<typeOrLocalOrThis>.<fn>.selector` in `abi.encodeWithSelector` and `abi.encodePacked` | `lowerSelectorBytes` resolves the referenced function or public state-variable getter declaration's 8-character `"functionSelector"` hex string and allocates a 4-byte memory buffer containing the left-aligned 32-bit selector word (`word * 16^56`, `size := 4`). `isPureSelectorReceiver` requires the receiver to be a contract/interface/library type (`type(contract ...)`), `this`, a literal, or a local/parameter variable (including `Contract(x)` casts around them); storage-variable receivers fail closed (`selector receiver must be a contract/interface type, this, or a local/parameter`) because unoptimized vs via-IR optimized `solc` differ on whether evaluating `stateVar.fn.selector` emits an `SLOAD`. Standalone `.selector` expressions outside `abi.encodeWithSelector` / `abi.encodePacked` fail closed. |
| `abi.encodeWithSelector(selector, args...)` as an encoded byte buffer (`keccak256(...)`, `bytes memory` locals, `abi.encodePacked(...)`) | Lowered by `lowerEncodedBytes`: for zero payload arguments, returns the 4-byte `lowerSelectorBytes` buffer directly; for one or more scalar arguments, validates and lowers each argument in order (`checkEncodingScalar`), stores their 32-byte words via `AbiEncoding.staticWords`, and concatenates the 4-byte selector prefix and `32 * n`-byte argument payload into a freshly allocated `(4 + 32 * n)`-byte buffer via `AbiEncoding.packedBuffer` and `AbiEncoding.copyBytes`. Non-byte-buffer uses of `abi.encodeWithSelector` fail closed with `abi.encodeWithSelector is only supported as a byte buffer`. |
| Extended Yul arithmetic, bitwise, comparison, and context builtins (`sdiv`, `smod`, `exp`, `byte`, `signextend`, `slt`, `sgt`, `caller`, `address`, `timestamp`, `number`, `chainid`) | `lowerYul` validates builtin name and arity before lowering arguments (`unsupported Yul builtin <fname>`), and lowers `sdiv`, `smod`, `byte`, `signextend`, `slt`, `sgt`, `caller`, `address`, `timestamp`, `number`, and `chainid` to their exact `Expr` counterparts (and `exp(a, b)` to `Expr.externalCall "exp" [a, b]`). `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses` include `.smod`, `.byte`, and `.signextend` with reflexive `rfl` arm-pin lemmas `evalExpr_smod_arm`, `evalExpr_byte_arm`, and `evalExpr_signextend_arm`. |
| Located diagnostics for `<addr>.code`, `abi.decode`, and low-level calls / `FunctionCallOptions` | `<addr>.code` fails closed with `external contract code reads are outside this slice`; `abi.decode(...)` fails closed with `abi.decode is outside this slice`; and `<addr>.call`/`staticcall`/`delegatecall`/`transfer`/`send` and `fn{value: ...}(...)` (`FunctionCallOptions`) fail closed with `external contract calls are outside this slice`. |

### Development slice: dynamic scalar-array and string parameters, string locals/helpers, and `selfbalance` / `tx.origin` context reads

| Supported Solidity | Lowering boundary |
| --- | --- |
| Root and helper `T[] calldata` / `T[] memory` scalar array parameters (`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`) | Root `T[] calldata` parameters validate the ABI head, `uint64` length bound, and `32 * length` payload tail via `AbiLowering.scalarArrayCalldataHead`; root `T[] memory` parameters and `calldata`-to-`memory` helper arguments materialize and validate every element word via `AbiLowering.scalarArrayMemoryHead` / `AbiLowering.materializeCalldataScalarArray`. Supports `arr.length`, `arr[i]` (with `Panic(0x32)` bounds check and calldata element validation via `AbiLowering.readScalarArrayElement`), `for (uint256 i = 0; i < arr.length; i++)`, and internal helper forwarding. Nested arrays, narrow signed element arrays (`int8[]`–`int248[]`), `bytes[]` / `string[]`, and array element writes fail closed. |
| Root and helper `string calldata` / `string memory` parameters, `string memory` locals, `bytes(s)` / `string(b)`, and `bytes(s).length` | Root `string calldata` and `string memory` parameters decode via `AbiLowering.bytesCalldataHead` and `AbiLowering.bytesMemoryHead` (`ParamType.string`). Non-reassigned `string memory` locals and `string memory` helper parameters lower to retained `(pointer, size)` byte buffers (`stringBuffers`), supporting string literals, `string(abi.encodePacked(...))`, and single-return `string memory` helpers (`inlineStringFn`). `bytes(s).length` lowers to the buffer's byte length, and `s` / `bytes(s)` can be hashed (`keccak256`) or concatenated in `abi.encodePacked(...)`. Reassigned `string` locals fail closed. |
| `address(this).balance`, `payable(address(this)).balance`, `tx.origin`, and Yul `selfbalance()` / `origin()` | `address(this).balance`, `payable(address(this)).balance`, and Yul `selfbalance()` lower to `Expr.selfBalance`; `tx.origin` (`referencedDeclaration == -15`, `t_magic_transaction`) and Yul `origin()` lower to `Expr.txOrigin`. Covered by `Coverage.exprCovered`, `Quote.quoteExpr`, and `TransactionAccess.expressionAccesses` with reflexive `rfl` arm-pin lemmas `evalExpr_selfBalance_arm` and `evalExpr_txOrigin_arm`. External account `<addr>.balance` reads (`external account balance reads are outside this slice`) and `tx.gasprice` (`unsupported transaction context member gasprice`) fail closed. |

### Development slice: `bytes memory` parameters/locals/helpers, `.length` on byte buffers, `bytes.concat` / `string.concat`, `abi.encodeWithSignature`, and `abi.encodeCall`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Root and helper `bytes memory` parameters, `bytes calldata`-to-`bytes memory` copies, and single-return `bytes memory` helpers | Root `bytes memory` parameters decode and materialize calldata into memory at entry via `AbiLowering.bytesMemoryHead`, registering a retained `(pointer, size)` buffer in `byteBuffers` (`pointer := memoryPointer + 32`, `size := lengthBinding`). Initializing a `bytes memory` local or `bytes memory` helper parameter from a `bytes calldata` parameter copies the calldata words into freshly allocated memory via `AbiEncoding.reserve` and `Stmt.forEach`; passing a string literal (`literal_string`) or `bytes memory` buffer to a `bytes memory` helper parameter binds its `(pointer, size)` descriptor in the callee frame; and single-return internal/private/public `bytes memory` helpers inline via `inlineStringFn` (including expression-statement calls whose side-effect prelude is preserved). Indexing (`b[i]`) and reassigning `bytes memory` locals fail closed. |
| `.length` on `bytes memory` locals/parameters and inline encoded byte-buffer expressions | `lowerMember` lowers `<expr>.length` on any `bytes` / `bytes memory` / `bytes calldata` expression (`byteBuffers`, `calldataBytes`, `bytes(s)`, `bytes.concat(...)`, `abi.encode(...)`, `abi.encodePacked(...)`, `abi.encodeWithSelector(...)`, `abi.encodeWithSignature(...)`, `abi.encodeCall(...)`, and `bytes memory` helper calls) to `{ pre := buf.pre, expr := buf.size }`. Direct `.length` on `string` without `bytes(...)` conversion remains rejected by `solc`. |
| `bytes.concat(...)` and `string.concat(...)` builtins | Verified as `ElementaryTypeNameExpression` (`bytes` or `string`) `.concat` calls with `referencedDeclaration == none`. `bytes.concat` accepts `bytes`, `bytes memory`, `bytes calldata`, `bytes32`, `bytes4`, and `literal_string` arguments; `string.concat` accepts `string`, `string memory`, `string calldata`, and `literal_string` arguments. Both lower via `lowerPacked` (evaluating arguments right-to-left to match `solc --via-ir`, allocating a zero-padded output buffer via `AbiEncoding.packedBuffer`, and copying each argument's exact byte length via `AbiEncoding.copyBytes`). Non-byte-buffer uses of `bytes.concat` / `string.concat` and unsupported argument types (such as `uint256`) fail closed with located diagnostics. |
| `abi.encodeWithSignature(sig, args...)` and `abi.encodeCall(ContractOrInterface.fn, (...))` as encoded byte buffers | `abi.encodeWithSignature` lowers `sig` (`string` or string literal) as a byte buffer, computes the 4-byte selector word `keccak256(sigPtr, sigSize) & (0xffffffff * 16^56)` into a 4-byte buffer, validates and lowers each scalar payload argument (`checkEncodingScalar`), and concatenates selector + `32 * n` argument words via `encodeSelectorAndWords`. `abi.encodeCall` resolves the target `ContractOrInterface.fn` `FunctionDefinition` and its 8-hex-char `"functionSelector"` via `lowerMemberFunctionSelector` (requiring a pure contract/interface/library type, `this`, literal, or local/parameter receiver), checks that the second argument's tuple component count matches the target declaration's parameter count, converts each scalar argument to its declared parameter type via `convert pty argTy` (rejecting out-of-range narrow unsigned integer literals), and concatenates the 4-byte selector and `32 * n` words via `encodeSelectorAndWords`. Non-byte-buffer uses and non-scalar payload types fail closed. |

### Development slice: unnamed root dynamic `bytes` and `string` returns (`Stmt.returnBytes`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| Unnamed root `returns (bytes memory)` / `returns (bytes calldata)` and `returns (string memory)` / `returns (string calldata)` | Supported when a root function declares a single unnamed `bytes` or `string` return parameter (`functionDynamicBytesReturn?`) and each reached root `Return` expression satisfies `canLowerDynamicBytesReturnExpr`: string/hex literals, root `bytes` / `string` parameters (`calldata` or `memory`), constant `bytes` / `string` state variables, `bytes(...)` / `string(...)` conversions, `string.concat(...)`, `abi.encode(...)`, `abi.encodePacked(...)`, `abi.encodeCall(...)`, or single-return internal/private/public `bytes memory` / `string memory` helper calls (`_concat`, etc.). Lowers the return expression via `lowerEncodedBytes` into a fresh `_verity_memret_<stem>` pair (`_data_offset := buf.pointer`, `_length := buf.size`), runs any modifier post-placeholder statements (`env.rootPost`), and emits `Stmt.returnBytes "_verity_memret_<stem>"`. `Denote.returnBytesWords` and `Compile.compileStmt` read 32-byte words from memory when `name.startsWith "_verity_memret_"` and right-zero-pad the final partial word (`32 :: length :: paddedWords`), covered by `Coverage.stmtCovered`, `Quote.quoteStmt`, and `TransactionAccess.statementAccesses` with reflexive `rfl` arm-pin lemma `execStmt_returnBytes_arm`. Named dynamic `bytes` / `string` root return parameters, missing root returns, and parameter names starting with `_verity_memret_` fail closed with located diagnostics. |

### Development slice: `string` and `bytes` storage variables (`encoding == "bytes"`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `string` and `bytes` storage state variables (`layout.encoding == "bytes"`, `numberOfBytes == 32`) | Registered in `ImportedContract` with `FieldType.uint256` at their `solc` storage slot (`storageBytesVars`), while `Expr.storageArrayElement field slotExpr` and `Stmt.setStorageArrayElement field slotExpr value` on scalar `FieldType.uint256` fields denote and compile computed-slot `sload`/`tload` and `sstore`/`tstore` directly at `evalExpr slotExpr` (`Denote.evalExpr`, `Denote.execStmt`, `ExpressionCompile.compileStorageArrayElement`, `StorageWrites.compileSetStorageArrayElement`, `SourceSemantics.evalExpr`, `SourceSemantics.execStmt`, `Coverage`, `Quote`, `TransactionAccess`). |
| Storage `string` / `bytes` length reads (`b.length`, `bytes(s).length`, `bytes(string(b)).length`), memory materialization (`lowerStorageBytesRead`), whole-value writes (`s = ...`, `b = ...`), and `delete s` / `delete b` | `lowerStorageBytesLength` decodes the packed Solidity storage header word `raw = sload(slot)` (reverting with `Panic(0x22)` / `0x4e487b710000000000000000000000000000000000000000000000000000000000000022` when `(raw & 1) == ((raw & 255) / 2)` for `0 < (raw & 255) < 64`), returning `(raw & 255) / 2` for short values (`(raw & 1) == 0`) and `raw / 2` for long values (`(raw & 1) != 0`). `lowerStorageBytesRead` allocates a 32-byte-aligned memory buffer via `AbiEncoding.reserve` and either stores `raw & ~255` (short `< 32` bytes) or copies `(len + 31) / 32` words starting at `keccak256(slot)` via `Stmt.forEach` (`keccak256(abi.encode(uint256(slot))) + i`), enabling storage `string` / `bytes` values in `return`, local `string memory` / `bytes memory` initializers, helper arguments, `keccak256(...)`, `abi.encodePacked(...)`, and `bytes.concat` / `string.concat`. `lowerStorageBytesWrite` and `lowerStorageBytesDelete` validate the old storage header (`Panic(0x22)`), zero out any previously occupied long-storage words (`oldWords > newWords` or `newLen < 32`), and write either the packed short header `(firstWord & ~mask) \| (len * 2)` or the long header `len * 2 + 1` plus cleaned payload words at `keccak256(slot) + i`. Storage `bytes` indexing (`b[i]`), `.push` / `.pop`, storage-pointer locals, non-statement assignments, and reads shadowed by unsupported locals/parameters fail closed with located diagnostics. |

### Development slice: multi-statement `InlineAssembly`, Yul locals & full-word local/parameter assignments, `tstore`, `addmod` / `mulmod`, and `*=`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Multi-statement `InlineAssembly` blocks in root, single-return helper, void/multi-return helper, and loop bodies (`lowerAssemblyStmts`) | Supports sequential `YulVariableDeclaration` (`let x := expr` or default-zero `let x`), single-target `YulAssignment` (`x := expr`) to block-scoped Yul locals, the active single-return helper result (`checkYulReturnTarget` + `cleanHelperResultExpr`), or unshadowed full-word (`uint256`, `int256`, `bytes32`) writable Solidity scalar locals and helper/modifier parameters (`inlineAssemblyAssignedIds`), and `YulExpressionStatement` `tstore(slot, val)` (`Stmt.tstore`, covered by `Coverage.executableStmtCovered`, `Coverage.abiHeaderPreservingStmt`, `Quote.quoteStmt`, and `TransactionAccess.statementAccesses` with reflexive `rfl` arm-pin lemma `execStmt_tstore_arm`). Yul assignments to narrow Solidity locals/parameters (`uint8`–`uint248`, `address`, `bool`, `enum`), storage `.slot` / `.offset` references, multi-variable Yul declarations/assignments, and unsupported Yul statements (`if`, `for`, `switch`, `leave`, `mstore`, `sstore`, `revert`) fail closed with located diagnostics. |
| Yul `addmod(a, b, m)` / `mulmod(a, b, m)` and Solidity global `addmod(a, b, m)` / `mulmod(a, b, m)` | `lowerYulAddmod` computes exact 512-bit modular addition `(a + b) % m` (returning `0` when `m == 0` in Yul) via `aMod = a % m`, `bMod = b % m`, `diff = m - bMod`, and `aMod < diff ? aMod + bMod : aMod - diff`. `lowerYulMulmod` computes exact 512-bit modular multiplication `(a * b) % m` (returning `0` when `m == 0` in Yul) via a 256-iteration binary Russian-peasant modular doubling loop (`Stmt.forEach`). Solidity global `addmod` (`referencedDeclaration == -2`) and `mulmod` (`referencedDeclaration == -16`) convert their three arguments to `uint256` in source order, emit `Panic(0x12)` when `m == 0`, and delegate to `lowerYulAddmod` / `lowerYulMulmod` (both in expressions and discarded expression statements). |
| Compound multiplication assignment (`*=`) | Supported on declaration-bound scalar locals, writable helper/modifier parameters (`isCompoundAssignOp`), scalar storage fields, scalar mappings, and unsigned mapping-struct members for `uint8`–`uint256` and `int256`, using `checkedMul` / `checkedSignedMul` in checked mode and wrapping 256-bit (or `2^bits - 1` masked) multiplication in `UncheckedBlock`. |

### Development slice: Yul scratch-space `mstore` / `keccak256`, prefix/postfix `++` / `--`, `bytes32` shifts, and `bytes32` / `int256` / `address` constants

| Supported Solidity | Lowering boundary |
| --- | --- |
| Yul scratch-space `mstore(0x00, v)` / `mstore(0x20, v)` and `keccak256(off, size)` in `InlineAssembly` (`lowerAssemblyStmts`, `lowerYul`) | `lowerAssemblyStmts` admits `mstore(off, val)` when `off` is a pure literal `0` (`0x00`) or `32` (`0x20`), emitting `Stmt.mstore (.literal off) valVal.expr` and recording `yulScratch0` / `yulScratch32` in the active `InlineAssembly` block (`Env.yulScratch0`, `Env.yulScratch32`). `lowerYul` admits `keccak256(off, size)` (`Expr.keccak256`) over `(0, 32)`, `(32, 32)`, or `(0, 64)` only when the corresponding scratch-space word(s) have already been written in the same Yul block (`keccak256 requires scratch-space words 0x00..0x3f to be written in the same Yul block`), preventing reads of uninitialized or ABI-managed memory. Non-scratch `mstore` offsets or non-literal `keccak256` ranges fail closed (`only scratch-space mstore at 0x00 or 0x20 is supported`, `only scratch-space keccak256 over 0x00..0x3f is supported`). |
| Prefix (`++x`, `--x`) and postfix (`x++`, `x--`) increment/decrement in expressions and expression statements (`lowerIncDecExpr`) | Supported on writable `uint8`–`uint256` and `int256` scalar locals and helper/modifier parameters (`bodyCompoundAssignedIds`), scalar storage fields, scalar mappings (1 or 2 keys), and unsigned mapping-struct scalar members. Evaluates the target's prior value into `oldVar`, applies `combineCompound ("+=" \| "-=") ty (.localVar oldVar) (.literal 1)` (preserving checked `Panic(0x11)` vs `UncheckedBlock` wrapping), writes back the updated value, and yields the updated value for prefix (`++x`, `--x`) or `oldVar` for postfix (`x++`, `x--`). `assignmentIn` includes `++` and `--` so multi-operand / multi-argument expressions with side-effecting increments or decrements fail closed unless evaluation order is explicit. |
| `bytes32` shifts (`<<`, `>>`, `<<=`, `>>=`) and `bytes32` / `int256` / `address` constant state variables (`numericConstants`) | `lowerBinary`, `combineCompound`, and `lowerCompoundAssignment` support `<<`, `>>`, `<<=`, and `>>=` on `bytes32` with unsigned shift amounts (`Expr.shl rhs lhs` / `Expr.shr rhs lhs`). `numericConstants` and `lowerRef` admit `bytes32`, `int256` / `int`, and `address` / `address payable` `constant` declarations, converting the initializer via `convert declared (← mType initializer) (← lowerExpr initializer) initializer` while rejecting non-empty initializer preludes and narrow signed/fixed-bytes constant types (`int8`–`int248`, `bytes1`–`bytes31`). |

### Development slice: dynamic memory scalar array allocation/writes (`new T[](len)`), extended mapping keys/struct members, and terminal root named-return `InlineAssembly`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Dynamic memory scalar array allocation (`T[] memory a = new T[](len)`), element writes (`a[i] = val` / `delete a[i]`), and pure index preludes (`a[idx++]`) | `lowerLocal` supports non-reassigned `T[] memory` declarations initialized with `new T[](len)` when `T` is `uint8`–`uint256`, `address` / `address payable`, `bool`, or `bytes32` (`newArrayElementType?`). Evaluates `len` to `uint256`, guards `len <= 2^64 - 1` (`Panic(0x41)`), initializes free-memory pointer `0x40` to `0x80` if zero, checks `32 + 32 * len` allocation overflow (`Panic(0x41)`), bumps `0x40`, stores `len` at `ptr`, zero-initializes `len` words via `Stmt.forEach`, and registers an `inMemory := true` `ScalarArrayParam` in `scalarArrays`. `lowerEffect` supports `a[i] = val` and `delete a[i]` on `inMemory := true` scalar arrays with `i < a.length` bounds checks (`Panic(0x32)`) and boolean `0`/`1` normalization. `lowerRef` `IndexAccess` on `.scalarArray` allows index expressions with empty base preludes (such as `leaves[leafPos++]` and `hashes[hashPos++]`). Signed/nested `new` array allocations, reassigned array locals, and `calldata` array element writes fail closed. |
| Extended mapping key types (`mappingKey`) and mapping struct member types (`buildField`, `memberRead`, `lowerEffect`) | `mappingKey` accepts `address`, `address payable`, `contract` / `interface` types, `bytes32`, `int256`, `bool`, `enum` types, and `uint8`–`uint256` as one- and two-key mapping keys; narrow signed (`int8`–`int248`) keys are also admitted with sign extension; `bytes4` keys are supported, while other narrow fixed-bytes and reference keys fail closed. `buildField` accepts `uint8`–`uint256`, `int8`–`int256`, `address`, `address payable`, `contract` / `interface` types, `bytes32`, and `bool` as packed or full-word mapping-struct members, recording `booleanMembers` on `FieldInfo` so `memberRead` and `lowerEffect` normalize boolean struct member reads and writes with `Expr.logicalNot (.logicalNot ...)`. |
| Terminal root `InlineAssembly` assigning to a single named scalar return variable | When a root function has a single named scalar return parameter (`rootNamedReturn`), empty modifier post-statements (`rootPost.isEmpty`), and a terminal `InlineAssembly` statement that only assigns to the return declaration without reading it in Yul (`yulOnlyAssignsDecl`), `lowerRootStatements` routes the assembly block through `helperResult := some (rbinding, rty)` and `cleanHelperResultExpr` before `lowerRoot` emits `Stmt.returnValues`, matching `solc` ABI return masking on narrow return types (such as `address`) while rejecting Yul reads of narrow root return variables. |

### Development slice: user-defined value types (`type T is U`), direct parameter assignments, chained/conditional multi-returns, zero-arg custom-error helpers, Yul memory-array `keccak256`, and struct-array element helper calls

| Supported Solidity | Lowering boundary |
| --- | --- |
| User-defined value types (`type T is U`, `T.wrap(x)`, `T.unwrap(v)`, `using L for T`) | `index` records `UserDefinedValueTypeDefinition` nodes in `userValueTypeById` and `userValueTypes`, mapping both qualified (`Contract.T`) and unqualified (`T`) names to their underlying elementary type string `U`. When `U` is a supported non-enum scalar (`uint8`–`uint256`, `int256`, `address`, `bool`, `bytes32`), `mType` normalizes UDVT type descriptions to `U`, `selectFunction` matches either the UDVT name or `U`, and `lowerCall` lowers `T.wrap(arg)` and `T.unwrap(arg)` via `convert U (← mType arg) (← lowerExpr arg) arg`. UDVTs with unsupported underlying types (such as `bytes16` or `int128`) fail closed. |
| Direct scalar parameter assignments (`param = rhs`) in root functions, helpers, and modifiers | `bindHelperParams`, `lowerModifier`, and `lowerRoot` materialize scalar parameters into writable local bindings (`writableLocals`) whenever `bodyCompoundAssignedIds body` or `bodyDirectAssignedIds body` contains the parameter declaration ID (`||` instead of `&& !`), initializing the local to the incoming parameter value so both reads before assignment and subsequent `=` / compound assignments use the same mutable binding. `delete param` remains rejected (`only materialized scalar locals are writable` / `only declaration-bound scalar locals are writable`). |
| Chained and conditional multi-return statements (`return _pair(...);`, `return cond ? _pair(...) : (a, b);`) in helpers and roots | Both `lowerVoidHelperFrom` (when `multiHelperResults` is active) and `lowerRootStatements` (when `rootReturnTypes.size > 1`) route non-`TupleExpression` return expressions through `lowerMultiBranch` with expected component types, supporting direct multi-return helper forwarding and `Conditional` (`? :`) expressions whose branches are tuples or multi-return helper calls of matching arity. |
| Pure/view zero-argument scalar helper calls and `tx.origin` in custom-error revert arguments (`revert Unauthorized(_msgSender(), ...)`) | `isDirectErrorScalar` admits `tx.origin` (`referencedDeclaration == -26`) and zero-argument internal/private `pure` or `view` helper calls returning a single supported scalar (such as `_msgSender()`), while stateful (`nonpayable`/`payable`), parameterized, or external calls in custom-error arguments fail closed. |
| Yul `keccak256(add(arr, 0x20), mul(mload(arr), 0x20))` over dynamic memory scalar arrays (`yulMemoryArrayPayloadSlice?`) | `Env.yulMemoryArrays` maps unshadowed `T[] memory` variable names (`new T[](len)` locals and `T[] memory` parameters) to their `memoryPointer` binding (clearing entries on local/parameter shadowing or Yul `let` shadowing). In `lowerYul`, `keccak256(ptrNode, sizeNode)` recognizes `add(arr, 0x20)` (or `add(0x20, arr)`) paired with `mul(mload(arr), 0x20)` (or `mul(0x20, mload(arr))`) for the same `arr` identifier and lowers to `Expr.keccak256 (.add (.localVar arrayPtr) (.literal 32)) (.mul (.mload (.localVar arrayPtr)) (.literal 32))`. Mismatched array identifiers or arbitrary pointer arithmetic fail closed (`unsupported Yul keccak256 arguments`). |
| Passing struct-array elements (`market.collaterals[i]`) to internal struct helper parameters (`.abiElement` in `lowerCallArgs` / `bindHelperParams`) | `lowerCallArgs` lowers `IndexAccess` on a schema-validated struct array (`m.items[i]`, `.abiElement`) to `CallArg.abiElement`. `bindHelperParams` verifies that the element struct's AST declaration ID matches the callee parameter's struct declaration ID, binds `calldata`-to-`calldata` and `memory`-to-`memory` element pointers in `abiElements`, and materializes `calldata`-to-`memory` element arguments via `AbiRootLowering.materializeElementFromCalldata`. `memory`-to-`calldata` conversions fail closed. |

### Development slice: nested 1-key scalar mappings in storage structs, `bytes4` scalars, and `type(I).interfaceId`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Nested 1-key scalar mappings inside mapping-backed storage structs (`struct RoleData { mapping(address => bool) hasRole; ... }`) | `buildField` decodes `mapping(K => V)` members inside mapping-backed structs (`StructMappingInfo` with `wordOffset`, `keyType`, `valueType`, `valueBits`, `booleanValue`) when `K` is a supported `mappingKey` and `V` is a supported scalar (`uint8`–`uint256`, `int256`, `address` / contract / interface, `bytes32`, `bool`). Accessed struct mappings are recorded in `usedStructMappings` (removing them from `report.opaqueMembers` while keeping unreferenced struct mappings opaque) and enable the synthetic `_verity_raw_storage` (`FieldType.uint256`) slot channel (`usedRawStorage`). `computeStructMappingLeafSlot` hashes outer mapping key(s) via `keccak256(abi.encode(k, slot))`, adds `wordOffset`, and hashes `keccak256(abi.encode(innerKey, structSlot + wordOffset))`. `readStructMappingElement`, `writeStructMappingElement`, `lowerEffect`, `lowerCompoundAssignment`, and `lowerIncDecExpr` support scalar reads, `=`, `delete`, compound assignments, and `++`/`--` (with bit-width masking and boolean `0`/`1` normalization). Unindexed struct-mapping references and whole-struct `delete m[k]` on structs with mapping members fail closed (`cannot delete mapping struct with mapping members`). |
| `bytes4` scalar type (`ParamType.bytesN 4`, `BytesN 4`) | `paramType "bytes4" = some (.bytesN 4)` with `Word (BytesN 4)` accessor bridge, preserving canonical `"bytes4"` ABI signature rendering (`supportsInterface(bytes4)`, etc.). Root `bytes4` parameters enforce `solc`'s entry calldata check `(calldataload(offset) & (2^224 - 1)) == 0` (`bytes4Params`); named helper/root returns clean trailing bits via `cleanHelperResultExpr`; uninitialized `bytes4` locals default to `0`; `bytes4` constants (`numericConstants`) and `0xXXXXXXXX` hex literals (`convert "bytes4"`) left-align to `val * 16^56`; explicit casts support `bytes4(bytes32Val)` (`bitAnd (0xffffffff * 16^56)`), `bytes32(bytes4Val)`, `uint32(bytes4Val)` (`shr 224`), and `bytes4(uint32Val)` (`shl 224`); bitwise `&`, `\|`, `^`, `~`, `&=`, `\|=`, `^=` mask results to the upper 4 bytes (`0xffffffff * 16^56`); comparisons (`==`, `!=`, `<`, `>`, `<=`, `>=`) require both operands to be `bytes4` (rejecting implicit `int_const` operands); and `abi.encode`, `abi.encodePacked`, and `bytes.concat` accept `bytes4` scalars (`scalarPackedWidth "bytes4" = some 4`). |
| `type(I).interfaceId` constant evaluation (`lowerInterfaceId`) | Supported in `lowerExpr`, `checkEncodingScalar`, and `lowerErrorArguments` when `I` resolves to a `ContractDefinition` with `contractKind == "interface"`. Collects all `FunctionDefinition` nodes directly declared in `I`, parses each 8-hex-digit `"functionSelector"`, XORs the 32-bit selector words (`Nat.xor`), and left-aligns the result (`acc * 16^56`) as a `bytes4` literal. Non-interface contracts or missing function selectors fail closed with located diagnostics. |

### Development slice: top-level storage structs, flat scalar-member `memory` struct locals, whole-struct storage assignment/`delete`, standalone `.selector` expressions, Yul memory-array element loads, and Yul fixed-prefix `keccak256`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Top-level storage struct state variables (`RoyaltyInfo private _defaultRoyaltyInfo;`, `SPath.zero`) | `buildTopStructField` decodes top-level `t_struct(...)` layout items via `decodeStructLayoutMembers` (`keyCount = 0`). When a top-level struct is referenced, `importSlice` emits a scalar `Field` (`FieldType.uint256`, `slot = some (info.slot + member.wordOffset)`, `packedBits = member.packed`) per scalar/expanded-array member under `_verity_struct_<field>_<member>` (`topStructMemberFieldName`), while rejecting user storage declarations that start with `_verity_struct_`. `memberRead`, `lowerEffect`, `lowerCompoundAssignment`, `lowerIncDecExpr`, `computeStructMappingLeafSlot`, and `lowerLocal` support member reads/writes, nested struct-mapping/fixed-array accesses, `storage` local aliases, and whole-struct reads/writes/`delete` on `SPath.zero`. |
| Flat scalar-member `memory` struct locals, positional `StructName(...)` constructors, and whole-struct storage assignment/`delete` (`FlatStructLocal`, `lowerFlatStructValue`, `writeWholeStorageStruct`) | Local `StructName memory s = init;` declarations where `StructName` has only supported non-enum scalar members (`paramType mTy`) and `init` is either a positional `structConstructorCall` (`StructName(a, b)`) or a scalar-member storage struct path (`_tokenRoyaltyInfo[id]`, `_defaultRoyaltyInfo`) materialize one writable scalar local binding per member (`flatStructs`, `FlatStructLocal`). `s.member` reads and writes the corresponding scalar binding, `s = rhs` updates all member bindings from a positional constructor or storage struct read (rejecting local-to-local `s2 = s1` aliasing so value-vs-reference semantics can never diverge), and `writeWholeStorageStruct` lowers `storageStruct = rhs` and `delete storageStruct` across all scalar members (`keyCount` `0`, `1`, or `2`). Named struct constructor arguments (`StructName({b: 2, a: 1})`) and structs with mapping/array/opaque members fail closed. |
| Standalone `.selector` member access as a `bytes4` scalar expression (`this.onERC721Received.selector`, `IERC1155Receiver.onERC1155Received.selector`, `CustomError.selector`) | `lowerSelectorMemberAccess` lowers `.selector` `MemberAccess` nodes with `typeDescriptions.typeString == "bytes4"` when the base is a pure receiver `MemberAccess` (`isPureSelectorReceiver`: contract/interface type, `this`, or a pure local/parameter) referencing a function, public state variable (`"functionSelector"`), or custom error (`"errorSelector"`), or an `Identifier` referencing a custom error, left-aligning the 8-hex-digit selector to `word * 16^56`. Non-pure receivers or non-member bases fail closed. |
| Yul 32-byte-strided memory-array element loads (`res := mload(add(add(arr, 0x20), mul(pos, 0x20)))`, `yulMemoryArrayElementLoad?`) | In `lowerYul`, `mload(addr)` matches `add(add(arr, 0x20), mul(pos, 0x20))` (with commutative operand order for `add` and `mul`) when `arr` resolves in `yulMemoryArrays` to an unshadowed `T[] memory` binding (`uint256[]`, `address[]`, etc.), lowering to `Expr.mload (.add (.add (.localVar arrayPtr) (.literal 32)) (.mul posExpr (.literal 32)))`. Non-`0x20` strides or non-array pointers fail closed (`unsupported Yul builtin mload`). |
| Yul fixed-prefix scratch-space and free-memory `keccak256` blocks (`MessageHashUtils.toEthSignedMessageHash(bytes32)`, `MessageHashUtils.toTypedDataHash(bytes32, bytes32)`, `lowerYulPrefixKeccakBlock?`) | Recognizes (1) 3-statement Yul blocks `mstore(0x00, "<k-byte prefix>"); mstore(k, msgHash); dst := keccak256(0x00, k + 0x20)` (`0 < k < 32`) and lowers them to exact scratch-space packing (`mstore(0, prefixWord \| (msgHash >> (8*k)))`, `mstore(32, msgHash << (8*(32-k)))`, `keccak256(0, k + 32)`), and (2) 5-statement EIP-712 Yul blocks `let ptr := mload(0x40); mstore(ptr, "<k-byte prefix>"); mstore(add(ptr, k), domSep); mstore(add(ptr, k + 0x20), structHash); dst := keccak256(ptr, k + 0x40)` (`0 < k < 32`) and lowers them to free-memory-pointer-preserving writes at `mload(64)` followed by `keccak256(ptr, k + 64)`. Mismatched offsets or lengths fail closed. |

### Development slice: `storage` struct / `bytes` / `string` helper parameters, flat scalar-member `memory` struct helper parameters, and `bytes32(bytes)` / `bytes4(bytes)` casts

| Supported Solidity | Lowering boundary |
| --- | --- |
| Internal/private/library `StructName storage` helper parameters (`BitMaps.BitMap storage`, `DoubleEndedQueue.Bytes32Deque storage`, `using L for S` receiver syntax) | `lowerCallArgs` lowers top-level (`SPath.zero`), 1-key (`SPath.one`), and 2-key (`SPath.two`) storage struct paths and `storage` struct local/parameter aliases (`Ref.structSlot`) to `CallArg.storageStruct`, capturing mapping keys into fresh temporaries at the call boundary (`captureStoragePath`). `bindHelperParams` verifies that the argument's `FieldInfo.structType` matches the callee parameter's `t_struct(...)` type and binds the resolved `SPath` in `structAliases`, enabling scalar member reads/writes/`delete`/compound assignments, nested struct-mapping accesses (`BitMaps`), fixed-array accesses, whole-struct `delete` (`DoubleEndedQueue.clear`), and forwarding to nested `storage` struct helpers. Top-level structs whose only members are nested mappings (`BitMaps.BitMap`) omit redundant scalar field definitions while emitting `_verity_raw_storage`. Reassigning a `storage` struct parameter (`p = other`) fails closed (`reassigned storage struct parameters are outside this slice`). |
| Internal/private/library `StructName memory` helper parameters for flat scalar-member structs (`FlatStructLocal` / `CallArg.flatStruct`) | When a `StructName memory` helper parameter is not covered by the existing `AbiRootLowering` calldata/memory root-ABI schema, `lowerCallArgs` accepts a `FlatStructLocal` identifier, a positional `StructName(...)` constructor, or a storage-to-memory copy of a scalar-member storage struct (`lowerFlatStructValue`), evaluating and converting all scalar members at the call site into `CallArg.flatStruct`. `bindHelperParams` binds fresh per-member local variables in `flatStructs` and rejects helpers that reassign the struct parameter (`reassigned struct parameters are outside this slice`). Storage-to-memory copies of structs with mapping/array/opaque members fail closed (`storage struct with non-scalar members cannot be copied to memory in this slice`). |
| Internal/private/library `bytes storage` and `string storage` helper parameters (`ShortStrings.byteLengthWithFallback`, `ShortStrings.toStringWithFallback`, `ShortStrings.toShortStringWithFallback`) | `lowerCallArgs` resolves top-level `bytes` / `string` storage variables and `storage` parameter aliases (`storageBytesVars`) to `CallArg.storageBytes`. `bindHelperParams` binds the `StorageBytesInfo` descriptor in the callee's `storageBytesVars`, enabling `.length` / `bytes(store).length`, memory materialization (`lowerStorageBytesRead`), whole-value storage writes (`store = val`, when the target is a direct storage variable rather than a storage-pointer parameter), `delete store`, and forwarding to nested helpers. Because `=` on a `string storage` / `bytes storage` helper parameter (`t_string_storage_ptr` / `t_bytes_storage_ptr`) rebinds the local storage pointer in Solidity rather than writing to storage, helpers that assign to a `bytes storage` or `string storage` parameter fail closed (`reassigned storage bytes parameters are outside this slice` / `reassigned storage string parameters are outside this slice`). |
| Explicit `bytes32(bytesVal)` and `bytes4(bytesVal)` casts (`ShortStrings.toShortString`) | `lowerConversion` supports `bytes32(...)` and `bytes4(...)` when the inner argument is a `bytes` / `bytes memory` / `bytes calldata` / `bytes storage` expression (`lowerEncodedBytes`). Evaluates the byte buffer once (`ptr`, `size`), loads the first 32-byte word when `size > 0` (`0` when `size == 0`), zeroes trailing bytes beyond `size` when `size < 32` (`word & ~(2^(8*(32 - size)) - 1)`), and masks to the upper 4 bytes (`0xffffffff * 16^56`) for `bytes4(...)`. |

### Development slice: ERC-7201 / `StorageSlot` raw-slot struct pointers (`r.slot := slot`), `StorageSlot.StringSlot` / `StorageSlot.BytesSlot` dynamic storage, `ShortStrings.toString`, and `$` identifiers

| Supported Solidity | Lowering boundary |
| --- | --- |
| ERC-7201 namespaced storage and `StorageSlot` struct pointer helpers (`function _getVaultStorage() private pure returns (VaultStorage storage $) { assembly { $.slot := SLOT } }`, `StorageSlot.getAddressSlot(slot).value`, `SPath.rawSlot`) | `classifyStorageSlotReturnHelper` recognizes internal/private/library helpers that return a single named `StructName storage r` parameter and have a 1-statement `Block` containing a 1-statement `InlineAssembly` block `r.slot := expr` (`yulSlotAssignRhs?`). For struct definitions whose members are supported scalars, packed scalars (`buildRawStructField`, computing exact word and byte offsets via `solc`'s 32-byte packing rules), and 1-key or 2-key scalar mappings (`StructMappingInfo` with `innerKey2Type?`), `lowerStorageSlotPointerHelper` inlines the helper call, evaluates `expr` as a `uint256` slot binding, sets `usedRawStorage := true`, and returns `Ref.structSlot #[] (.rawSlot info slotBinding)`. `readRawSlotScalarMember` and `writeRawSlotScalarMember` read, mask, shift, sign-extend (`int256`), boolean-normalize, and pack/unpack scalar members on `_verity_raw_storage[baseSlot + wordOffset]`; `computeStructMappingLeafSlot` hashes `keccak256(abi.encode(k1, baseSlot + wordOffset))` (and `keccak256(abi.encode(k2, ...))` for 2-key mappings); and `lowerLocal`, `lowerCallArgs`, `writeWholeStorageStruct`, `lowerCompoundAssignment`, and `lowerIncDecExpr` support `StructName storage $ = _getStorage();`, helper forwarding, scalar/packed member updates, and whole-struct writes/`delete`. Nested struct-valued mappings inside ERC-7201 raw-slot structs or multi-statement slot-pointer assembly helpers fail closed with located diagnostics. |
| `StorageSlot.StringSlot` and `StorageSlot.BytesSlot` dynamic `string` / `bytes` storage wrappers (`StorageSlot.getStringSlot(slot).value`, `StorageSlot.getBytesSlot(slot).value`, `SPath.bytesSlot`) | When a `r.slot := expr` helper returns a `StructName storage` whose `StructDefinition` has a single `string` or `bytes` member named `value` (`classifyStorageSlotReturnHelper` returning `.bytesStorageSlot`), `lowerStorageSlotPointerHelper` yields `Ref.structSlot #[] (.bytesSlot slotBinding isString)`. `MemberAccess` `.value` resolves to `Ref.storageBytes pre { name := rawStorageFieldName, slotExpr := .localVar slotBinding, isString }` (`StorageBytesInfo.slotExpr`), enabling `.value.length` / `bytes(...value).length`, memory reads (`lowerStorageBytesRead`), whole-value writes (`StorageSlot.getStringSlot(slot).value = s`), `delete StorageSlot.getBytesSlot(slot).value`, and passing `.value` to `string storage` / `bytes storage` helpers (such as `ShortStrings.toStringWithFallback(sstr, StorageSlot.getStringSlot(slot).value)`). Wrapper structs with extra members or members other than `.value` fail closed (`StorageSlot bytes/string wrapper struct must have a single value member`). |
| `ShortStrings.toString(ShortString)` (`string memory str = new string(32); assembly { mstore(str, len) mstore(add(str, 0x20), sstr) }`, `yulShortStringsAllocPtrs`, `lowerYulShortStringStoreBlock?`) | `lowerLocal` admits `string memory s = new string(cap)` / `bytes memory b = new bytes(cap)` when `cap` is the literal `32`, reserving 64 bytes via `AbiEncoding.reserve`, storing initial length `32` and zeroed payload word, and registering `s` in `Env.yulShortStringsAllocPtrs` and `bytesVars`. `lowerYulShortStringStoreBlock?` recognizes the 2-statement `InlineAssembly` block `mstore(str, lenExpr); mstore(add(str, 0x20), wordExpr)` on an unshadowed `yulShortStringsAllocPtrs` buffer, updating `mstore(ptr, lenExpr)` and `mstore(ptr + 32, wordExpr)` and refreshing the `MemoryBuffer` length in `bytesVars` so returning `str` or passing `str` to `bytes(str)` / `keccak256` / `abi.encodePacked` observes the updated dynamic length. Non-`32` capacity literals or mismatched `mstore` targets fail closed (`only new string(32) / new bytes(32) for ShortStrings is supported in this slice`). |
| `$` in Solidity local variable and parameter identifiers (`VaultStorage storage $ = _getVaultStorage();`) | `lowerLocal` allows `$` alongside alphanumeric characters and `_` in Solidity identifier names, while `freshFor` sanitizes or falls back to `fresh` whenever a source name contains characters outside `[a-zA-Z0-9_]` so generated Yul variable names remain valid identifiers. |

### Development slice: dynamic scalar storage arrays (`T[]`), recursive nested storage structs, `Arrays.unsafeAccess`, `EnumerableSet` / `EnumerableMap`, and unnamed root dynamic scalar array returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Top-level and struct-member dynamic scalar storage arrays (`T[]`, `layout.encoding == "dynamic_array"`, `StructDynamicArrayInfo`) | `buildField`, `decodeStructLayoutMembers`, and `resolveRawStructInfo` decode 1-D dynamic storage arrays `T[]` (`dynamicStorageArrayElement?`: `uint8`–`uint256`, `int256`, `address` / contract, `bool`, `bytes32`) at top level (`FieldInfo.dynamicArrayElemType`), inside top-level or mapping-backed structs (`FieldInfo.structDynamicArrays`), and inside ERC-7201 raw-slot structs (`RawStructInfo.dynamicArrays`). Element packing (`dynamicStorageArrayElemLayout`: `perWord = max 1 (32 / (bits / 8))`) computes exact storage slot `keccak256(abi.encode(slot)) + index / perWord` and intra-word shift `((index % perWord) * bits)` on `_verity_raw_storage`. Supports `.length` (`readStorageDynamicArrayLength`), `arr[i]` reads (`readStorageDynamicArrayElement` with `Panic(0x32)` bounds check), `arr[i] = val` / `delete arr[i]` / compound assignments / `++` / `--` (`writeStorageDynamicArrayElement`), `arr.push(val)` and `arr.push()` (`pushStorageDynamicArray`, incrementing length and writing at `oldLen`), `arr.pop()` (`popStorageDynamicArray` with `Panic(0x31)` on empty array, clearing element `newLen`), `delete arr` (`deleteStorageDynamicArray`, zeroing `(len + perWord - 1) / perWord` slots and setting length to `0`), and storage-to-memory copies (`T[] memory m = arr;` and `T[] memory` helper arguments via `copyStorageDynamicArrayToMemory`). Multi-dimensional or struct-element dynamic storage arrays and whole-array assignment `arr = other` fail closed with located diagnostics. |
| Recursive nested struct members in storage structs (`struct UintSet { Set _inner; }`, `struct AddressToUintMap { Bytes32ToBytes32Map _inner; }`) and `StructName storage` return helpers | `decodeStructLayoutMembers` and `resolveRawStructInfo` recursively flatten nested `t_struct(...)` members using qualified member paths (`subPrefix.member` / `qualifySPathMember` / `appendSPathSub` for `SPath.zero`, `SPath.one`, `SPath.two`, and `RawStructSubStructInfo` word offsets for `SPath.rawSlot`), enabling arbitrary-depth `set._inner._values`, `map._inner._keys._inner._positions[k]`, and `$.borrowerSet` accesses. `inlineStorageRefFn` inlines internal/private/library helpers that return `StructName storage` or `T[] storage` pointers (`StorageSlot.getBytes32Slot`, `Arrays.unsafeAccess`). |
| `T[] storage` helper parameters, local aliases, `arr.slot` in `InlineAssembly`, and `uint256[] memory` / `bytes32[] memory` pointer reinterpretation (`EnumerableSet.values`) | `lowerCallArgs`, `bindHelperParams`, and `lowerLocal` bind non-reassigned `T[] storage` parameters and locals in `storageDynamicArrayVars` and expose `<name>.slot` in `Env.yulNames` (`Arrays.unsafeAccess(bytes32[] storage arr, uint256 pos)`). Single-return helpers returning `T[] memory` inline via `inlineScalarArrayFn` (supporting `return storageArr;`, `return memArr;`, and `return helper(...);`). `lowerYulScalarArrayAliasBlock?` recognizes the 1-statement `InlineAssembly` block `assembly ("memory-safe") { result := store }` in `EnumerableSet.values(UintSet storage)` / `values(AddressSet storage)` when `store` and `result` are unshadowed 32-byte-word memory scalar arrays (`bytes32[]`, `uint256[]`, `address[]`), rebinding `result` to `store`'s `memoryPointer` and `lengthBinding`. Reassigned `T[] storage` parameters or locals fail closed. |
| Unnamed root dynamic scalar array returns (`returns (T[] memory)`) | Supported when a root function declares a single unnamed `T[] memory` return parameter (`functionDynamicScalarArrayReturn?`). Non-empty root bodies lower each reached `Return` statement (`canLowerDynamicScalarArrayReturnExpr`: local `T[] memory` variable, storage `T[]` copy, or `T[] memory` helper call such as `activeTrancheIds.values()`) into a fresh `_verity_arrret_<stem>` pair (`_data_offset := ptr + 32`, `_length := len * 32`), run `env.rootPost`, and emit `Stmt.returnBytes "_verity_arrret_<stem>"` (`Denote.returnBytesWords` and `Compile.compileStmt` emit `32 :: wordCount :: words` for `_verity_arrret_`, matching `solc` ABI encoding of `T[]`). |

### Development slice: dynamic storage arrays of scalar-member structs (`S[]`), struct-valued mappings inside storage structs, `Checkpoints._unsafeAccess`, binary-search `while (low < high)` loops, named struct constructors, and flat-struct helper returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| Dynamic storage arrays of scalar-member structs (`S[]`, `Checkpoints.Checkpoint208[]`, `TrancheRecord[]`) at top level, inside storage structs, and inside ERC-7201 raw-slot structs (`FieldInfo.dynamicArrayStructId`, `StructDynamicArrayInfo.elemStructId`) | `buildField`, `decodeStructLayoutMembers`, and `resolveRawStructInfo` accept 1-D dynamic storage arrays `S[]` when `S` is a struct whose members are all supported scalars (`elemInfo.mappings.isEmpty && elemInfo.dynamicArrays.isEmpty && elemInfo.subStructs.isEmpty && !elemInfo.scalars.isEmpty && elemInfo.wordCount > 0`) and `base.numberOfBytes == elemInfo.wordCount * 32`. `storageDynamicStructElementPath` checks `index < len` (`Panic(0x32)`) and resolves `arr[index]` to `SPath.rawSlot elemSid (keccak256(abi.encode(arrSlot)) + index * wordCount)`, enabling member reads/writes, whole-struct reads (`S memory s = arr[i];`), whole-struct writes (`arr[i] = s`), and `delete arr[i]` (zeroing all `wordCount` slots). `pushStorageDynamicStructArray` lowers `arr.push(s)` and `arr.push()` (returning `SPath.rawSlot elemSid (keccak256(abi.encode(arrSlot)) + oldLen * wordCount)` for `S storage p = arr.push();` and chained `arr.push().member = v`), `popStorageDynamicArray` zeroes all `wordCount` slots of `newLen` on `arr.pop()` (`Panic(0x31)` on empty array), and `deleteStorageDynamicArray` zeroes `oldLen * wordCount` words on `delete arr`. `S[] storage` parameters and locals bind `(fieldName, slotExpr, elemTy, some elemSid)` in `storageDynamicArrayVars` and expose `<name>.slot` in `Env.yulNames`. Struct elements with nested arrays, mappings, or sub-structs fail closed (`unsupported storage encoding dynamic_array`). |
| Struct-valued mappings inside storage structs and ERC-7201 raw-slot structs (`mapping(address => Checkpoints.Trace208) delegateCheckpoints`, `StructMappingInfo.valueStructId`) | `resolveRawStructInfo` and `decodeStructLayoutMembers` accept `mapping(K => V)` struct members when `K` is a supported `mappingKey` and `V` resolves to a supported `RawStructInfo` (`valueStructId := some valSid`). Indexing `s.map[k]` in `lowerRef` hashes `leafSlot := keccak256(abi.encode(k, mapBaseSlot))` and returns `Ref.path (...) (.rawSlot valSid (.localVar leafSlot))`, enabling nested struct member, dynamic-array, and helper-receiver accesses such as `$.delegateCheckpoints[voter].push(...)` and `$.delegateCheckpoints[voter].upperLookup(...)`. |
| Prefix Yul statements before `result.slot := ...` in storage-pointer helpers (`Checkpoints._unsafeAccess`) | `inlineStorageRefFn` supports internal/private/library helpers returning `StructName storage result` whose `InlineAssembly` block executes prefix Yul statements (such as `mstore(0, self.slot)`) before a final `result.slot := add(keccak256(0, 0x20), pos)` assignment, lowering the prefix statements via `lowerYulStmtSlice` and returning `SPath.rawSlot retStructId (.localVar slotTmp)`. Statements after `result.slot := ...` or missing slot assignments fail closed (`storage pointer helper assembly must end with a single slot assignment`). |
| Binary-search `while (low < high)` / `while (high > low)` loops (`Checkpoints._upperBinaryLookup`, `Checkpoints._lowerBinaryLookup`) | `lowerWhile` recognizes `while (low < high)` and `while (high > low)` over distinct writable unsigned integer locals/parameters `low` and `high` of matching bit width (`isBinarySearchMidpointExpr`, `isBinarySearchStepStmt`): the loop body must be `[VariableDeclarationStatement mid = midpoint(low, high), IfStatement ...]` where `midpoint(low, high)` is `(low + high) / 2`, `(low + high) >> 1`, `(low & high) + (low ^ high) / 2`, `low + (high - low) / 2`, or a 2-argument pure helper returning that midpoint (`Math.average(low, high)`), and the `if / else` branches assign `high = mid` in one branch and `low = mid + 1` (or `1 + mid`) in the other while leaving `low`, `high`, and `mid` otherwise unmodified. Lowers to `let bound := sub high low; forEach iter bound [ite (lt low high) body []]`, which executes at most `high - low` iterations (and strictly halves `high - low` on every active step). Non-narrowing branches or modified midpoint variables fail closed. |
| Named struct constructor arguments (`StructName({fieldB: b, fieldA: a})`) and helpers returning flat `StructName memory` (`inlineFlatStructFn`) | `lowerFlatStructValue` supports named `structConstructorCall` arguments (`names.size == args.size`) when every argument is pure/stateless (`!statefulCallIn arg && !assignmentIn arg`), evaluating each argument once into a temporary in call-site order and assembling member values in struct declaration order (rejecting stateful or assignment arguments so evaluation order can never diverge). `inlineFlatStructFn` and `lowerVoidHelperFrom` (`flatStructHelperResult`) inline internal/private/library helpers returning a single flat scalar-member `StructName memory` (`Checkpoints.at`, `_makeRecord`), supporting named and unnamed return parameters, `if / else` early returns, conditional struct expressions (`cond ? s1 : s2`), member projections (`s.at(0)._value`), local initializations (`Checkpoint208 memory c = _unsafeAccess(...);`), and discarded flat-struct/multi-return helper calls in `lowerEffect`. |

### Development slice: bounded sign-flip self-calls (`wadExp(-x)`, `WadExpAndThreeKeyMappingSequence`), `while (low != high)` binary search with `unchecked` blocks, 3-key scalar and struct mappings, and top-level fixed-size unsigned scalar storage arrays (`uintN[L]`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| Bounded 1-step `int256` sign-flip self-calls (`WadExpLib.wadExp(int256 x)`: `if (x < 0) return 1e36 / wadExp(-x);`, `inlineSignFlipSelfCallFn?`, `inlineSelfSignFlipTarget`) | `inlineSignFlipSelfCallFn?` recognizes single-return internal/private/library helpers with one `int256` parameter `x` (neither directly nor compound-assigned in the body) whose leading statement is `if (x < 0)` (or `if (0 > x)`) with an empty `else` branch, where the `true` branch unconditionally returns an expression containing a single self-call `fn(-x)` (`containsSelfNegCall` / `countCallsToId` == 1) and the remaining statements after the `if` contain zero self-calls (`countCallsToId` == 0). Lowers by evaluating the non-negative (`false`) continuation once for `x >= 0` and once for `-x` inside the `x < 0` branch (binding `inlineSelfSignFlipTarget := some (fnId, paramId, negResultVar)` so `fn(-x)` resolves to `negResultVar` without recursion). General recursive calls or self-calls in the non-negative continuation still fail closed (`recursive helper call <name>`). |
| Binary-search `while (low != high)` / `while (high != low)` loops with `low == 0` at loop entry and `unchecked { ... }` loop bodies (`WadExpLib.ratioToLevel`, `Env.zeroInitLocals`, `unwrapUncheckedBlockStmts`) | `Env.zeroInitLocals` tracks local variables initialized to literal `0` (`uintN low = 0;` or uninitialized default `uintN low;`) and clears membership whenever a statement can assign or mutate the local (`stmtModifiedIds`). `lowerWhile` admits `while (low != high)` and `while (high != low)` alongside `<` / `>` when `lowId ∈ env.zeroInitLocals` (failing closed with `binary-search while (low != high) requires low to be zero at loop entry` when `low` is non-zero or modified before the loop), because `0 = low <= high` and `mid = midpoint(low, high) < high` whenever `low < high`, so both `high = mid` and `low = mid + 1` preserve `low <= high` and terminate in at most `bits` iterations. Both the outer `while` body and the inner `if / else` branches unwrap `UncheckedBlock` wrappers (`unwrapUncheckedBlockStmts`) while preserving unchecked arithmetic semantics during statement lowering. |
| Three-key scalar and struct mappings (`mapping(K1 => mapping(K2 => mapping(K3 => V)))`, `SPath.two` with hashed outer pair) | `mappingSpine` accepts `1`, `2`, or `3` keys from `mappingKey` (`address` / contract / interface, `bytes32`, `int256`, `bool`, `enum`, `uint8`–`uint256`), rejecting 4+ keys (`unsupported mapping key count 4`). For 3-key mappings (`info.keyTypes.size == 3`), `lowerRef` lowers triple-indexed accesses `m[k1][k2][k3]` by hashing the outer two keys into a single synthetic first-key slot `outerHash := keccak256(abi.encode(k2, keccak256(abi.encode(k1, slot))))` (`computeNestedMappingSlot`) and routing the third key `k3` through the 2-key storage path (`SPath.two info.name (.localVar outerHash) k3Val.expr`, emitted as `FieldType.mapping2` in `importSlice`). Supports scalar reads, `=`, `delete`, compound assignments, `++` / `--`, and struct-valued 3-key mappings (including `storage` struct aliases, member reads/writes, nested struct mappings/arrays, whole-struct assignment/`delete`, and helper arguments). Partial indexing (`m[k1]` or `m[k1][k2]` on a 3-key mapping) fails closed. |
| Top-level fixed-size 1-D unsigned scalar storage arrays (`uintN[L]`, `layout.encoding == "inplace"`, `SPath.zero`) | `buildField` decodes top-level `t_array(t_uintN)L_storage` state variables (`1 <= L <= 32`) via `fixedUnsignedArrayElement?`, expanding each element `i ∈ [0, L)` into a packed or full-word `Member` `__solidity_element_<i>` (`slotOffset = (i * bits) / 256`, `packed = PackedBits` when `bits < 256`) and emitting per-element scalar fields `_verity_struct_<field>___solidity_element_<i>` in `importSlice` (`!info.fixedArrays.isEmpty`). `lowerExpr`, `lowerRef`, `lowerLocal`, `lowerCallArgs`, and `lowerEffect` support `.length` (as constant `L`), `arr[idx]` reads and `arr[idx] = val` / `delete arr[idx]` writes with `idx < L` `Panic(0x32)` bounds guards and constant-index fast paths, `uintN[L] memory snap = arr;` and `uintN[L] memory` helper arguments (`copyStorageFixedArrayToMemory`), and whole-array `delete arr` (zeroing all `L` element members). Signed or multi-dimensional top-level fixed storage arrays fail closed (`unsupported storage type ...`). |

### Development slice: `mapping` values of dynamic `string` and `bytes` (`ERC721URIStorage`), dynamic `new bytes(len)` / `new string(len)` allocations, Yul `mstore8`, `while (true)` division/shift loops (`Strings.toString` / `Strings.toHexString`), and `bytes1`–`bytes32` literal constants in Yul

| Supported Solidity | Lowering boundary |
| --- | --- |
| 1-key and 2-key `string` mappings and 2-key `bytes` mappings (`mapping(uint256 => string) private _tokenURIs`, `mapping(address => mapping(uint256 => bytes)) public scopedPayloads`) | `buildField` decodes `encoding == "bytes"` (`numberOfBytes == 32`) mapping leaf types for 1-key and 2-key `string` mappings and 2-key `bytes` mappings (`bytesStorage := true`, `stringStorage := rawLeafType == "string"`), while preserving the rejection of 1-key `mapping(K => bytes)` (`unsupported mapping value encoding bytes`). `resolveStorageBytesTarget?`, `lowerEncodedBytes`, `lowerEffect`, `lowerLocal`, `lowerCallArgs`, and `lowerPublicStateVarGetter` compute the leaf header slot via `computeSPathBaseSlot` (`keccak256(abi.encode(k, slot))` or 2-key `keccak256`) and route reads (`lowerStorageBytesRead`), length queries (`bytes(m[k]).length`, `m[k1][k2].length`), writes (`m[k] = val`, rejecting stateful/assignment RHS when the key prelude is non-empty), `delete m[k]`, `string storage` / `bytes storage` local aliases (`string storage _tokenURI = _tokenURIs[tokenId];`) and helper arguments (`_writeScopedPayload`, `StorageSlot.getBytesSlot`), and synthesized `public` mapping getters through `_verity_raw_storage`. |
| Dynamic `new bytes(len)` and `new string(len)` memory allocations in `unchecked` blocks (`Strings.toString`, `Strings.toHexString`) | In `lowerLocal` (`isNewBytesInit && (← get).unchecked`), `bytes memory buf = new bytes(len)` and `string memory buf = new string(len)` evaluate `len` as an unsigned word, guard `len <= 2^64 - 1` (`Panic(0x41)`), allocate a 32-byte length header plus `32 * ((len + 31) / 32)` zero-initialized payload bytes at `mload(64)` with `uint64` free-memory overflow guards (`Panic(0x41)`), register `(pointer := headerPtr + 32, size := len)` in `byteBuffers` / `stringBuffers`, and bind `buf` to `headerPtr` in `Env.yulNames` so inline assembly can address the ABI header at `buf` and payload bytes starting at `add(buf, 32)`. Unchecked-outside `new bytes(len)` allocations without a `ShortStrings` 32-byte assembly consumer remain rejected. |
| Yul `mstore8(addr, val)` in `InlineAssembly` and `bytes1`–`bytes32` string/hex literal constants in Yul (`Strings.HEX_DIGITS`) | `lowerYulStmtSlice` lowers `mstore8(addr, val)` to an exact read-modify-write on the containing 32-byte word (`wordAddr := addr & ~31`, `shift := 8 * (31 - (addr & 31))`, `mstore(wordAddr, (mload(wordAddr) & ~(0xff << shift)) \| ((val & 0xff) << shift))`). `index` and `bindYulExternalConstants` admit `bytes1`–`bytes32` `constant` state variables initialized with string/hex literals (`bytes16 private constant HEX_DIGITS = "0123456789abcdef"`), left-aligning the hex payload to a 256-bit word (`word * 16^(64 - hex.length)`) in `Env.yulNames` for `byte(idx, HEX_DIGITS)`. `lowerStringHelperStmts` supports multi-statement `string memory` / `bytes memory` helpers containing `UncheckedBlock`, `ForStatement`, `WhileStatement`, `InlineAssembly`, `IfStatement` (including early-return or revert branches), and `RevertStatement`. |
| Bounded `while (true)` division/right-shift loops with `if (v == 0) break;` (`Strings.toString`) and `int_const` subtraction folding (`(1 << 128) - 1` in `Math.log256`) | `lowerWhile` supports `while (true)` loops whose body contains no `return`, updates an unsigned writable local `v` (`uintN`, `bits <= 256`) only in the penultimate statement via `v /= d` / `v = v / d` (`d >= 2` literal) or `v >>= k` / `v = v >> k` (`1 <= k < 256` literal), and ends with `if (v == 0) break;` (with no other `break` or `continue`), lowering to a `doneVar`-guarded `Stmt.forEach` bounded by `bits` iterations. `lowerBinary` folds non-negative `int_const` subtractions `a - b` when `a >= b` and `a - b < 2^256`. |

### Development slice: `Strings.toHexString` (all overloads), `Strings.toStringSigned`, `Strings.equal`, `Arrays.findUpperBound`, `BitMaps.setTo`, fixed-bytes indexing (`HEX_DIGITS[idx]`), `bytes1` casts, `bytes memory` element writes (`buffer[i] = ...`), and decrementing `for` loops

| Supported Solidity | Lowering boundary |
| --- | --- |
| Fixed-bytes indexing (`b[idx]` on `bytes1`–`bytes32`, `HEX_DIGITS[value & 0xf]`) and `bytes1` casts (`bytes1("0")`, `bytes1(uint8)`, `uint8(bytes1)`, `bytes1(bytes32)`, `bytes32(bytes1)`) | `lowerRef` and `lowerExpr` admit `bytes1`–`bytes32` literal `constant` declarations (`numericConstants`) as left-aligned 256-bit words (`word * 16^(64 - hex.length)`), and lower `base[idx]` on any pure/stateless `bytes1`–`bytes32` value with an unsigned index `idx` to a `idx < W` bounds check (`Panic(0x32)`) and `Expr.shl 248 (Expr.byte idx base)` (a left-aligned `bytes1` word). `lowerCast` supports `bytes1` casts from 1-byte string/hex literals (`byteVal * 2^248`), `uint8` (`(x & 0xff) << 248`), `bytes32` / `bytes4`, and `0xXX` hex integer literals, as well as `uint8(bytes1)` (`x >> 248`) and `bytes32(bytes1)` / `bytes4(bytes1)`. Stateful or assignment fixed-bytes base/index expressions and multi-byte string literal casts to `bytes1` fail closed with located diagnostics. |
| Dynamic `bytes memory` element writes (`buffer[i] = val` / `delete buffer[i]`) and `new bytes(a + b)` allocations (`Strings.toHexString(uint256, uint256)`, `Strings.toStringSigned`) | `lowerLocal` admits `bytes memory buf = new bytes(len)` / `string memory buf = new string(len)` outside `unchecked` blocks when `len` is a binary arithmetic expression (`2 * length + 2`), checking `len` before allocating a header-backed `(pointer := headerPtr + 32, size := len)` buffer with `buf` registered in `Env.yulNames`. `lowerEffect` supports `buffer[idx] = rhs` and `delete buffer[idx]` on `new bytes(...)` buffers (`byteBuffers` with `yulNames` entry) when `idx` is a pure/stateless unsigned expression and `rhs` is a `bytes1` expression or 1-byte string/hex literal (`"0"`, `"x"`, `HEX_DIGITS[...]`), enforcing `idx < buffer.size` (`Panic(0x32)`) and performing a single-byte read-modify-write at `buffer.pointer + idx`. |
| Decrementing `for (uint256 i = start; i > lower; --i)` loops (`Strings.toHexString`) | `lowerFor` supports `for (uint256 i = start; i > lower; --i)` (and `i--` / `i -= 1`) when `i` is not modified in the loop body and `lower` is an invariant literal, parameter, or unassigned local, evaluating `start` once, computing `count := start > lower ? start - lower : 0`, and executing `Stmt.forEach iterIdx count` with `i := start - iterIdx` bound in `values` and `yulNames`. |
| `Arrays.findUpperBound(uint256[] storage, uint256)`, `BitMaps.setTo`, and `Strings.equal(string memory, string memory)` | `lowerWhile` binary-search recognition (`classifyBinarySearchBranch`) unwraps `UncheckedBlock` inside `if / else` branches (`unchecked { low = mid + 1; }` in `Arrays.findUpperBound`) and accepts helper calls (`Math.average(low, high)`) and storage dynamic array reads (`array.unsafeAccess(mid).value > element`) in the branch condition. `lowerYul` lowers `mstore(0x00, a)` / `keccak256(a, b)` in inline assembly (`Strings.equal` via `keccak256(add(a, 0x20), mload(a)) == keccak256(add(b, 0x20), mload(b))`) when `a` and `b` are header-backed `string` / `bytes` bindings in `yulNames` (`bindHelperParams` binds `string memory` / `bytes memory` parameters in `yulNames` to a materialized `[length, payload...]` header block). |

### Development slice: `ECDSA` Yul signature unpacking (`mload(signature)` / `mload(add(signature, 0x20/0x40/0x60))`), provably-bounded Yul narrow-local assignments (`v := byte(0, ...)`), custom-error scalar-cast arguments (`ECDSA._throwError`), and `StorageSlot.getStringSlot(bytes32)` / `StorageSlot.getBytesSlot(bytes32)`

| Supported Solidity | Lowering boundary |
| --- | --- |
| Yul byte-buffer header and word loads (`mload(b)` and `mload(add(b, offset))`, `ECDSA.tryRecover(bytes32, bytes memory)`, `yulByteBufferLoad?`) | `bindRoot`, `bindHelperParams`, and `lowerLocal` record unshadowed `bytes memory` and `string memory` variables in `Env.yulMemoryStructs`. When `b` is not bound in `Env.yulNames` (`yulByteBufferByName?`), `lowerYul` lowers `mload(b)` to `{ pre := buf.pre, expr := buf.size }` and `mload(add(b, offset))` / `mload(add(offset, b))` for 32-byte-aligned positive word offsets (`offset >= 32 && offset % 32 == 0`, `yulPositiveWordOffsetLiteral?`) to `Expr.mload (.add buf.pointer (.literal (offset - 32)))`. Zero or unaligned offsets fail closed (`unsupported Yul builtin mload`). |
| Yul assignments of provably-bounded expressions to narrow non-enum scalar locals (`uint8 v; assembly { v := byte(0, mload(add(signature, 0x60))) }`, `isProvablyBoundedYulExpr`) | `lowerYulDirectAssignmentTarget` admits Yul assignments to narrow non-enum scalar locals/parameters (`bool`, `uint8`–`uint248`, `address`) when the lowered RHS expression is provably bounded by `2^bits` (`isProvablyBoundedYulExpr`: `.literal n` with `n < 2^bits`, `.byte _ _` for `bits >= 8`, `.lt`/`.gt`/`.slt`/`.sgt`/`.eq`/`.logicalNot` for `bits >= 1`, `.bitAnd` with a mask `< 2^bits`, `.shr` by `>= 256 - bits`, or `.mod` by `0 < m <= 2^bits`). Arbitrary unmasked Yul expressions (`narrow := add(narrow, 1)`, `v := mload(...)`) continue to fail closed (`Yul assignment to narrow local <name> is unsupported`). |
| Scalar `typeConversion` casts in custom-error revert arguments (`revert ECDSAInvalidSignatureLength(uint256(errorArg))`) | `lowerErrorArguments` accepts single-argument `typeConversion` calls whose inner expression is an identifier bound in `Env.values` (such as `uint256(errorArg)` where `errorArg` is `bytes32`), lowering and converting the argument via `convert errorParamType (← mType argument) (← lowerExpr argument) argument`. |
| Raw `bytes32` slot wrappers `StorageSlot.getStringSlot(bytes32 slot)` and `StorageSlot.getBytesSlot(bytes32 slot)` (`inlineStorageStructFn`) | When an internal/private/library storage-pointer helper returns a 1-member wrapper struct whose only member has type `string` or `bytes` (any member name, e.g. `struct { string value; }`) via a 1-statement `r.slot := slot` assembly block (`prefixYstmts.isEmpty && sMembers.size == 1` and the member type is `string`/`bytes`), `inlineStorageStructFn` binds `slot` to a fresh local and returns `SPath.bytesSlot ("", .localVar slotBinding) isString`, enabling member reads, `.length`, writes, `delete`, and `string storage` / `bytes storage` helper arguments on raw `bytes32` slots. |

### Development slice: `Create2.computeAddress`, `Clones.predictDeterministicAddress`, `keccak256(_msgData())`, and bounded `DoubleEndedQueue.Bytes32Deque` `popFront` / `popBack` `while` loops (`Governor._checkGovernance`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `Create2.computeAddress(bytes32, bytes32, address)` and `Create2.computeAddress(bytes32, bytes32)` (`lowerYulPrefixKeccakBlock?`) | Recognizes the 7-statement Yul block `let ptr := mload(0x40); mstore(add(ptr, 0x40), bytecodeHash); mstore(add(ptr, 0x20), salt); mstore(ptr, deployer); let start := add(ptr, 0x0b); mstore8(start, 0xff); addr := and(keccak256(start, 85), 0xffffffffffffffffffffffffffffffffffffffff)` and lowers it to 3 word-aligned 32-byte writes at `ptr = mload(64)` (`word0 = (prefixByte << 248) \| ((deployer & (2^160 - 1)) << 88) \| (salt >> 168)`, `word1 = (salt << 88) \| (bytecodeHash >> 168)`, `word2 = bytecodeHash << 88`) followed by `keccak256(ptr, 85)` and the target assignment. Mismatched offsets, prefix widths, or hash lengths fail closed. |
| `Clones.predictDeterministicAddress(address, bytes32, address)` and `Clones.predictDeterministicAddress(address, bytes32)` (`lowerYulPrefixKeccakBlock?`) | Recognizes the 8-statement Yul block `let ptr := mload(0x40); mstore(add(ptr, 0x38), deployer); mstore(add(ptr, 0x24), 0x5af43d82803e903d91602b57fd5bf3ff); mstore(add(ptr, 0x14), implementation); mstore(ptr, 0x3d602d80600a3d3981f3363d3d373d3d3d363d73); mstore(add(ptr, 0x58), salt); mstore(add(ptr, 0x78), keccak256(add(ptr, 0x0c), 0x37)); predicted := and(keccak256(add(ptr, 0x43), 0x55), 0xffffffffffffffffffffffffffffffffffffffff)`, packing the 55-byte EIP-1167 creation code into 2 aligned words at `ptr` and `ptr + 32`, binding `initHash := keccak256(ptr, 55)`, packing the 85-byte CREATE2 preimage into 3 aligned words at `ptr + 64`, `ptr + 96`, and `ptr + 128`, and evaluating `keccak256(ptr + 64, 85)`. |
| `keccak256(_msgData())` and zero-argument `bytes calldata` / `bytes memory` `msg.data` helpers (`lowerMsgDataBuffer`, `lowerEncodedBytes`, `lowerStringHelperStmts`) | `lowerEncodedBytes` and `lowerStringHelperStmts` accept zero-argument internal/private/public helper calls returning `bytes calldata` or `bytes memory` whose single `return` expression resolves to `msg.data` (via `inlineMsgDataFn`), materializing the full `calldatasize`-byte transaction calldata (selector word plus calldata words) into an aligned memory buffer via `lowerMsgDataBuffer` while keeping direct `keccak256(msg.data)` rejected at `msg.data`. |
| Bounded-range pop `while` loops such as `DoubleEndedQueue.Bytes32Deque` `popFront` / `popBack` (`while (_governanceCall.popFront() != msgDataHash) {}`, `Governor._checkGovernance`, `lowerWhile`, `boundedRangePopBounds?`) | `lowerWhile` recognizes `while (q.pop() != target) {}` (the call on either side of `!=`) when `pop` is a 1-argument storage helper over a struct of two `uint128` bounds and one `mapping(uint128 => bytes32)` (any helper, struct, and member names) whose body is structurally a range pop: `uint128 i = q.lo; if (i == q.hi) revert ...; value = q.data[i]; [delete q.data[i];] q.lo = i + 1;` (low end) or `uint128 i = q.hi; if (i == q.lo) revert ...; --i; value = q.data[i]; [delete q.data[i];] q.hi = i;` (high end). The low/high bound members are derived from that body. `q` must resolve to a storage path with an empty key prelude, `target` is a pure/stateless `bytes32` expression (`!statefulCallIn target && !assignmentIn target`), and the loop body is empty (`bodyStmts.isEmpty`). Lowers to `bound := ((hi - lo) & (2^128 - 1)) + 1`, `done := 0`, and `Stmt.forEach loopVar bound [ite (done == 0) (popPre ++ targetPre ++ [ite (popVal == targetVal) [done := 1] []]) []]`, so matching elements terminate the loop and missing elements pop until `lo == hi` and revert (e.g. `QueueEmpty()`) on the `(len + 1)`-th iteration. Helpers without the empty-range revert or bound advance are not recognized; non-empty loop bodies or stateful/non-`bytes32` targets fail closed with located diagnostics. |

### Development slice: `bytes calldata` / `msg.data` slices (`data[start:end]`), `Governor._isValidDescriptionForProposer` (unaligned Yul tail `mload`, `bytes` element reads, bounded tail-window `for` loops), `bytes1`–`bytes31` locals/helpers/casts (`bytes12`, `bytes20`, `ERC2771Context`), and `MemberAccess` tuple assignments (`AccessManager`)

| Supported Solidity | Lowering boundary |
| --- | --- |
| `bytes calldata` and `msg.data` / `_msgData()` slices (`data[start:end]`, `data[start:]`, `data[:end]`, `data[:]`, `lowerCalldataSlice?`) | `lowerCalldataSlice?` recognizes `IndexRangeAccess` on unshadowed `bytes calldata` parameters (`calldataBytes` with `inMemory == false`), direct `msg.data`, and zero-argument `bytes calldata` helpers returning `msg.data` (`_msgData()`). Evaluates optional unsigned `start` (default `0`) and `end` (default `base.length`) bounds once, enforces `start <= end` and `end <= base.length` (reverting with empty returndata on out-of-bounds slices, matching `solc`), and yields `(slicePre, baseOffset + start, end - start, isMsgData)`. Supported in `.length` (`MemberAccess`), `bytesN(slice)` casts (`1 <= N <= 32` via `lowerBytesToFixedBytes`, stitching the 4-byte selector word and calldata payload when `isMsgData` and `offset < 4`), `abi.decode(slice, (...))` (`lowerAbiDecodeItems`, when `!isMsgData`), and memory materialization (`lowerEncodedBytes`, copying `len` bytes into an aligned memory buffer for `bytes(slice)`, `keccak256(slice)`, `abi.encode*`, and `bytes.concat`). Signed slice bounds or `IndexRangeAccess` on `memory` / `storage` arrays fail closed. |
| `Governor._isValidDescriptionForProposer`: unaligned Yul byte-buffer tail `mload(add(buf, sub(len, k)))`, dynamic `bytes` / `bytes(string)` element reads `b[i]`, and bounded tail-window `for (uint256 i = len - K; i < len; ++i)` loops | In `yulByteBufferLoad?`, `mload(add(buf, sub(lhs, k)))` (and `mload(add(sub(lhs, k), buf))`) on a headerless `EncodedBytes` buffer (`yulByteBufferByName?`) with literal `1 <= k <= 32` computes `addr := buf.pointer + (lhs - (32 + k))` and reconstructs the unaligned 32-byte word from the two surrounding aligned words (`(mload(addr & ~31) << (8 * (addr & 31))) \| (mload((addr & ~31) + 32) >> (256 - 8 * (addr & 31)))`); `k == 0` or `k > 32` fails closed (`unsupported Yul builtin mload`). In `lowerExpr`, `IndexAccess` `b[idx]` on dynamic `bytes` (`bytes memory`, `bytes calldata`, `bytes storage`, `bytes(str)`) evaluates `buf ← lowerEncodedBytes b`, checks `idx < buf.size` (`Panic(0x32)`), and loads the single byte at `buf.pointer + idx` as a left-aligned `bytes1` word (`shl 248 (byte (addr & 31) (mload (addr & ~31)))`). `lowerFor` and `lowerHelperFrom` support `for (uint256 i = bound - K; i < bound; ++i)` (`1 <= K <= 256` literal, `bound` invariant), running `K` iterations with `i := (bound - K) + iterIdx` (including early `if (...) return ...;` inside single-return helpers). |
| Narrow fixed-bytes (`bytes1`–`bytes31`) locals, helper parameters/returns, `bytesN("...")` string literal casts (`N < 32`), and `bytes12` / `bytes20` integer/address conversions (`ERC2771Context._msgSender()`, `Votes`) | `localParamType`, `cleanHelperResultExpr`, and `lowerYulDirectAssignmentTarget` support `bytes1`–`bytes31` (`ParamType.bytesN w`, left-aligned to `256 - 8*w` bits), while keeping root ABI parameters and storage fields restricted to `bytes4` and `bytes32`. `lowerCast` supports `bytesN("...")` / `bytesN(hex"...")` for `1 <= N < 32` when the literal byte length is `<= N` (leaving `bytes32("...")` rejected), `bytesN(bytesSliceOrMemory)` (`1 <= N <= 32`), `bytes12(uint96)` / `uint96(bytes12)` (`shl 160` / `shr 160`), `bytes20(uint160)` / `uint160(bytes20)` / `bytes20(address)` / `address(bytes20)` (`shl 96` / `shr 96`), and widening/truncating conversions between `bytes12` / `bytes20` and `bytes32`. `lowerBinary` supports `==`, `!=`, `<`, `<=`, `>`, `>=`, `&`, `\|`, and `^` on matching `bytesN` types (rejecting implicit `int_const` operands), and `AbiEncoding` packs `bytes1`–`bytes32` values by their exact byte width (`scalarPackedWidth`). |
| Tuple assignment with `MemberAccess` storage or flat-struct targets (`(_roles[roleId].grantDelay, effect) = _roles[roleId].grantDelay.withUpdate(...)`, `AccessManager`) | `lowerEffect` `TupleExpression` assignment supports `MemberAccess` components alongside `Identifier` components, resolving each `MemberAccess` target against flat `memory` struct locals (`flatStructs`), ERC-7201 raw-slot storage structs (`SPath.rawSlot`), and top-level or 1-/2-/3-key mapping-backed storage structs (`SPath.zero`, `SPath.one`, `SPath.two`) with boolean `0`/`1` normalization and key-capture prelude validation. |

### Development slice: `mapping(bytes4 => ...)` in storage structs and top-level/nested mappings, `bytes4[]` parameters and `abi.decode(..., (bytes4[]))`, `bytes calldata` helper arguments and slices (`AccessManager`), `bytes1` ABI parameters/returns, and `bytes4`/`bytes1` event parameters

| Supported Solidity | Lowering boundary |
| --- | --- |
| `mapping(bytes4 => ...)` in storage structs and top-level/nested/3-key mappings (`AccessManager.TargetConfig.allowedRoles`, `_targets[target].allowedRoles[selector]`, `AccessManager.getTargetFunctionRole`, `AccessManager.canCall`) | `mappingKey` accepts `bytes4` (`Some .bytes32` in the 256-bit storage key model, left-aligned in the upper 4 bytes), enabling `bytes4` keys in top-level 1-/2-/3-key mappings (`mappingSpine`), struct-member 1-/2-key mappings (`decodeStructLayoutMembers`), and ERC-7201 raw-slot struct mappings (`resolveRawStructInfo`). `lowerRef` converts `IndexAccess` keys on `mapping(bytes4 => ...)` bases via `convert "bytes4"`, and `computeSPathBaseSlot`, `computeNestedMappingSlot`, and `computeStructMappingLeafSlot` left-align `bytes4` keys (`k` in upper 32 bits, lower 224 bits zeroed) when hashing `keccak256(abi.encode(k, slot))`, matching `solc` storage slot layout. |
| `bytes4[]` calldata/memory parameters, locals, helper arguments, and `abi.decode(..., (bytes4[]))` (`AccessManager.setTargetFunctionRole`) | `scalarArrayElement?` accepts `bytes4[]` (`(.uint256, .uintN 256)`). Calldata `bytes4[]` indexing in `lowerRef`, calldata-to-memory materialization in `AbiLowering.scalarArrayMemoryHead` and `AbiLowering.materializeScalarArray`, and `abi.decode(..., (bytes4[]))` in `abiDecodeScalarGuard?` enforce right-padding (`bitAnd word (2^224 - 1) == 0`, reverting with empty returndata on dirty lower 224 bits). `lowerLocal` and `lowerEffect` convert `bytes4` element reads and writes on `bytes4[]` memory arrays. |
| `bytes calldata` helper arguments (`_canCallExtended(caller, data)`, `_getAdminRestrictions(_msgData())`) and slices on helper `bytes calldata` parameters (`data[0:4]`, `data[0x04:0x24]`, `data[0x24:0x44]`) | `lowerCallArgs` and `bindHelperParams` allow passing `bytes calldata` expressions (`_msgData()`, `msg.data`, `data[start:end]`, or `bytes calldata` parameters) to `bytes calldata` helper parameters (`CallArg.byteBuffer` / `CallArg.calldataBytes`). `lowerCalldataSlice?` returns `(slicePre, offsetExpr, lenExpr, fromCalldata, isMsgData)` and admits unshadowed `bytes calldata` helper parameters bound in `byteBuffers` or `calldataBytes` (`inMemory == true`), routing `bytesN(slice)` (`lowerBytesToFixedBytes`), `abi.decode(slice, (...))` (`lowerAbiDecodeDataSource`), and `lowerEncodedBytes` through `readAbiDecodeWord fromCalldata` (`calldataload` when `fromCalldata == true`, unaligned-safe `mload` reconstruction when `fromCalldata == false`). |
| `bytes1` root/helper parameters, returns, `abi.decode(..., (bytes1))`, `abi.encode*`, and `bytes.concat` (`Strings.tryHexToUint(bytes1)`) | `paramType` maps `"bytes1"` to `ParamType.bytesN 1` (`TransactionAccess` and `SequenceRunner` decode/encode `bytesN 1` as left-aligned `v * 2^248` with lower 248 bits zeroed). `importSlice` and `abiDecodeScalarGuard?` guard `bitAnd word (2^248 - 1) == 0` on calldata and `abi.decode` inputs; `cleanHelperResultExpr` masks `bytes1` returns to the top byte; and `lowerPackedArgument` (`abi.encodePacked`, `bytes.concat`) writes 1-byte `bytes1` payloads directly from the left-aligned word without shifting. |
| `bytes4` and `bytes1` event parameters (`event TargetFunctionRoleUpdated(address indexed target, bytes4 selector, uint64 indexed roleId)`) | `lowerEmit` and `SequenceRunner.observeEventValue` accept `.bytesN 4` and `.bytesN 1` event parameters when the argument is a matching direct root parameter reference (`.param _`, matching `Compiler.CompilationModel.ValidationEvents`), masking observed topic/data words to their upper 32 or 8 bits (`value - value % 2^(256 - 8*w)`). Non-parameter `bytes4` / `bytes1` event expressions fail closed (`narrow event arguments currently require a matching direct parameter`). |
### Development slice: SSTORE2-style `create2` code storage and struct event parameters

| Supported Solidity | Lowering boundary |
| --- | --- |
| `bytes memory code = abi.encodePacked(PREFIX, abi.encode(s)); assembly { addr := create2(0, add(code, 0x20), mload(code), salt) }` in roots and inlined library/internal helpers (`lowerYulCreate2?`, `lowerYulValue`) | `startsWithInitcodeTemplate` records a `bytes memory` local when its initializer is `abi.encodePacked` / `bytes.concat` whose first argument is a hex literal or hex constant accepted by `DenoteCreate2.templateCost` (inspected bytes; currently the 11-byte `PUSH0` and 13-byte `PUSH1 0` copy-and-return prefixes) and it is never reassigned. `create2` must be the whole value of a Yul assignment or `let`; the value must be the literal `0`, the offset `add(buf, 0x20)` / `add(0x20, buf)` and the size `mload(buf)` of the same local. It lowers to `Stmt.ecm (SolidityCreate2.module r) [0, buf.pointer, buf.size, salt]` and the expression `r & (2^160 - 1)`. `Denote.executeByteCreate2` reads the initcode from physical memory through `Create2Opcode.execute` (parent gas from `ByteCallEnvironment.gas`, Keccak through the model oracle), binds the address or zero, installs the expanded memory and commits the account transition; parent out-of-gas and static/size aborts halt with empty data, and unchecked initcode or missing gas is a payload-free instrumentation `.revert`. Functions whose only CEI barriers or reentrancy windows are these closed transports carry the unchecked obligations `solidity_closed_transport_cei` / `solidity_create2_initcode_reentrancy`. |
| `emit E(S s, bytes32 indexed id, ...)` with non-indexed struct parameters (`lowerStructEmit`) | Events with a struct-typed parameter take this path; scalar-only events keep `Stmt.emit`. Non-indexed arguments are memory struct identifiers (dynamic or static ABI schema) or scalars, encoded by the shared `lowerAbiEncodeArgs` (`abi.encode` lowering). Indexed parameters must be total `uint*` / `address` / `bool` / `bytes32` expressions, cleaned with `cleanHelperResultExpr`. Topic 0 is the declaration's `eventSelector`. The statement is `Stmt.ecm (SolidityLog.module E n) (topics ++ [ptr, size])`; `Denote.executeByteLog` records the topics as `indexedArgs` and the payload words as `args` and rejects non-word payloads as instrumentation errors. The sequence adapter reports such logs byte-exactly. |

Validation: `check_create2_struct_emit.py` replays the fixture and its `renamed` and `expanded` variants on source EVM, Denote and the compiled model. Deployment accounts are discovered from both EVM routes' CREATE2 opcode traces (`deployment.py`), and code, nonces and balances of every planned account, the caller's nonce, return data, storage and exact logs are compared; payloads stay small because Denote's closure-based physical memory makes byte copies quadratic in time. `check_create2_struct_emit_rejections.py` pins 17 located near-miss rejections and 8 positive controls, and `check_create2_struct_emit_mutations.py` holds ten runtime importer/Denote mutants and four admission-guard mutants.

### Development slice: `<address>.code.length` and optional-bool low-level calls

| Supported Solidity | Lowering boundary |
| --- | --- |
| `require(token.code.length > 0, NoCode());` and other `<addr>.code.length` reads on `address`-typed accounts (`lowerExtCodeSize`) | The account expression is lowered to an atom and read by `Stmt.ecm (SolidityExtCodeSize.module r) [addr]`, compiled to `let r := extcodesize(addr)`. `Denote.executeByteExtCodeSize` binds `DenoteExternalCode.extCodeSize world (Address.ofNat addr)` (`executeByteExtCodeSize_eq`); the legacy `Expr.extcodesize` and its `ContractState.codeSize` view are unchanged. `address(this).code.length` rejects because the executing contract's code differs between the source and compiled routes. The transport hands control to no account, so `eraseClosedTransports` erases it for the CEI check. |
| `(bool success, bytes memory returndata) = token.call(abi.encodeCall(IERC20.transfer, (to, amount)));` followed by the returndata-forwarding `if` and the optional-bool `require` (`lowerLowLevelCallSequence?`, hooked into `lowerRootStatements` and `lowerVoidHelperFrom`) | The three statements are matched structurally (`lowLevelCallMember?`, `isReturndataForwarding`, `isOptionalBoolValidation`, `lowLevelEncodeCallParts`); `success` and `returndata` may not be referenced elsewhere (`jsonMentionsDecl`). The receiver and encoded arguments are lowered in source order (stateful operands reject), converted to the function's parameter types, and emitted as `Stmt.ecm (SolidityLowLevelCall.optionalBoolModule r selector n) (target :: words)` followed by the `require`'s own `reason` on `r` (`lowerRequireWith`). `Denote.executeByteOptionalBoolCall` prepares the calldata with `prepareByteWordCall .call` (free pointer advanced after the call), runs `ByteExternalCall.executeChecked`, and dispatches on `classifyOptionalBoolCall`: forward the child's bytes, revert empty on malformed returndata, or bind the decoded word. `DenoteLowLevelCall` proves the request is `callBytesRequest` and that the result is `1` exactly when `decodeOptionalBoolCall` accepts. Functions whose reentrancy windows are only these calls, after which no storage is read or written and any scalar event arguments are storage-free, carry `reentrancyTrusted` with the unchecked obligation `solidity_trailing_low_level_call_reentrancy`. |

Validation: `check_external_code_and_low_level_call.py` replays the fixture and its `renamed` and `expanded` variants on source EVM, Denote and the compiled model against eleven `RecordingCallResponder` configurations (true, false, empty, invalid and short words, extra bytes, short/empty/long revert payloads), an account without code and the sender EOA; responders record the call count, calldata size and first four calldata words, so selector, argument encoding and committed callee writes are compared in storage. Denote receives the responders' deployed runtime code for code-length reads. `check_external_code_and_low_level_call_rejections.py` pins 19 located near-miss rejections and 7 positive controls, and `check_external_code_and_low_level_call_mutations.py` holds ten runtime importer/Denote/ECM mutants and five admission-guard mutants.

### Development slice: `<address>.code` and dynamic-struct `abi.decode` returns

| Supported Solidity | Lowering boundary |
| --- | --- |
| `abi.decode(pointer.code, (S))` and `bytes memory data = pointer.code;` on `address`-typed accounts (`lowerExtCodeCopy`, hooked into `lowerAbiDecodeDataSource` and the `bytes memory` local initializer) | The account is lowered to an atom and copied by `Stmt.ecm (SolidityExtCodeCopy.module r) [account]`; the buffer's data pointer `r + 32` and length `mload(r)` are bound. The compiled transport is solc's `external_code_at`: `extcodesize`, allocation of `roundUp(size) + 32` bytes at the free pointer (`Panic(0x41)` when the length or new free pointer exceeds 64 bits or wraps), the length word, then `extcodecopy(account, r + 32, 0, size)`. `Denote.executeByteExtCodeCopy` performs the same writes on physical memory from `DenoteExternalCode.accountCode` (address taken modulo `2^160`). `address(this).code` rejects because the executing contract's code differs between the source and compiled routes; `.code` keeps its located rejection everywhere else (`keccak256(a.code)`, `a.code[i]`). The transport hands control to no account, so `eraseClosedTransports` erases it for the CEI check. |
| `abi.decode(data, (S))` of a struct with dynamic array members from a `bytes memory` buffer (`parseAbiDecodeItem` → `AbiDecodeTypeItem.dynamicStruct`, `AbiMemoryDecode.materialize`) | Only structs that are not flat and whose complete `AbiSchema` contains unsigned scalars, dynamic arrays of unsigned scalars and dynamic arrays of flat scalar structs take this path; every other member keeps the existing `unsupported abi.decode struct member type` diagnostic. The decoder follows solc's `abi_decode_tuple_*_fromMemory`: one head word, the struct offset (`≤ 2^64 - 1`), a signed remaining-size check for the struct head, eager allocation, then members in declaration order: scalars are validated (`validator_revert_*`), arrays check their offset, `slt(header + 31, end)`, `Panic(0x41)` for lengths or allocations beyond 64 bits before the payload bound `data + length * elementSize ≤ end`, and flat-struct elements are separately allocated with their own remaining-size check. The result is a memory `MemParam` with the complete schema, so field reads and `abi.encode` use the existing memory-struct lowering. Calldata sources and additional decode targets reject. |
| `function f(...) external view returns (S memory) { return abi.decode(pointer.code, (S)); }`, `S memory s = abi.decode(...); return s;` and `return param;` for `S memory` parameters (`functionDynamicStructReturn?`, `lowerDynamicStructReturnValue`) | The model return type is `AbiSchema.paramType S`. The returned struct is encoded by `lowerEncodedMem` (the root-tuple branch of `abi.encode`) and returned by `Stmt.ecm SolidityReturnMemory.module [ptr, size]`, compiled to `return(ptr, size)`; `Denote.executeByteReturnMemory` stops with the buffer's words in `observedReturnWords` (non-word buffers are instrumentation errors). An unreachable `Stmt.revertEmpty` follows the transport because `Stmt.ecm` metadata cannot state termination for the compiler's exhaustive return analysis. Named returns, calldata structs, helper calls and other expressions reject. |

Validation: `check_extcodecopy_struct_decode.py` replays the fixture and its `renamed` and `expanded` (`bytes memory` local, decoded local plus `return`, memory alias) variants on source EVM, Denote and the compiled model. Code is stored by the checked CREATE2 transport, from canonical encodings and from 22 raw payloads around every decoder check (non-canonical, shared and backwards offsets, trailing bytes, dirty scalars, truncated heads and payloads, offsets beyond 64 bits, `Panic(0x41)` lengths and allocations, empty and short code), then read back by `load` (return of `abi.decode(pointer.code, (Spec))`), `summary` (field reads) and `echo` (memory parameter return); deployment accounts come from EVM CREATE2 traces. `check_extcodecopy_struct_decode_rejections.py` pins 14 located near-miss rejections and 8 positive controls, and `check_extcodecopy_struct_decode_mutations.py` holds 17 runtime importer/decoder/Denote/ECM mutants and five admission-guard mutants.

# Initcode execution groundwork

`Verity/Core/Model/InitCodeExecution.lean` executes the bytecode instructions in
the eleven-byte SSTORE2 deployment prefix with an explicit instruction bound.
The kernel proof `push11CopyReturn_returns_payload` composes nine intermediate
instruction lemmas and proves that the returned bytes equal the appended
payload. Byte-copy frame lemmas preserve reads outside the destination range.
This is deployment proof infrastructure: it adds no supported Solidity or Yul
construct by itself. The SSTORE2-style `create2` row above admits Yul `create2`
only over `bytes memory` buffers that start with these checked templates.

The account-world prerequisite now stores bounded nonces, balances, exact code
bytes and finite storage in `ContractState.accountWorld`. `DenoteCreate2`
executes the checked initcode templates and handles transfers, nonce increments,
collisions, deposit rules and child gas. Account frames and existing transaction
rollback include this metadata. The source-storage/account-storage bridge,
parent opcode charging, ABI/events, compiled-model route and importer lowering
remain required before CREATE2 is supported. Unsupported initcode is an
instrument error, never a fabricated successful deployment or Solidity revert.

`BytesObjectMemory` provides a byte-level immutable object representation:
big-endian length header, payload at base+32, zero padding and disjoint-write
frame proofs. Its EVM/Lean instrument observes source-created objects and
aliases after another allocation. This is a prerequisite, not new supported
Solidity: allocator/pointer identity, overflow and gas behavior, declaration
provenance, the canonical word-memory bridge and compiled-model integration
remain mandatory before admitting object-pointer Yul expressions.


### CREATE2 parent opcode composition prerequisite

`Create2ParentGas` charges the Osaka base cost, six-gas Keccak and two-gas
EIP-3860 initcode words, and quadratic memory expansion. Zero-length ranges
do not expand memory. Kernel lemmas establish the EIP-150 gas split,
conservation and bounded child refunds. `Create2Opcode.execute` derives the
child allowance from parent gas, reads initcode from actual byte memory,
executes the concrete account transition and refunds unused child gas. The
expanded memory zero-extends inactive bytes; no backing-function contents
beyond the old active range become visible. Static/size violations abort,
parent out-of-gas aborts, and nonaligned instrument memory is rejected.

`check_deployment_world --parent-opcode` compares actual EVM opcode memory,
parent continuation gas, child allowance and account transitions against Lean,
including nonce-limit prechecks. It supplies neither initcode bytes nor a child
gas allowance to the Lean opcode driver. This remains A/B calibration, not an
imported or compiled-model C campaign. Canonical Stmt integration, complete
frame gas tracking, source allocator/memory refinement, account/storage bridge,
ABI/revert/event observations and all exact-head release gates remain required.
No new Solidity construct or whole-EVM equivalence is claimed here.


### Canonical flat-storage/account coherence

Concrete account storage uses `Std.TreeMap` with kernel-checked read-after-write
and outside-frame laws. `writePhysicalSlot`, `writePhysicalSlots` and
`modifyPhysicalSlots` update flat persistent storage and the self account's
finite storage together. Batch transformers read the original world, including
when targets alias. These APIs preserve code, nonce, balance, caller metadata,
transient keys and legacy shadow channels. Legacy `writeSlot` and bulk lenses
retain their previous account-world frame; their regression is unchanged.

Canonical Denote flat scalar, packed, mapping-word and fixed-array write helpers
use the physical APIs. The reference `SourceSemantics` uses the same exact
physical transitions; the statements of `DenoteAgreement` and
`DenoteFunctionAgreement` are unchanged. `AccountStorageBridge` proves coherence
for single/batch/transformed writes and runtime-code commits to another account.
Old shadow-mapping/channel-wide compatibility operations are not asserted to
preserve this relation and must not be used as an exact deployment bridge.

The scalar differential adapters initialize finite storage through the physical
API. The sequence adapter verifies flat/account agreement for every touched or
requested persistent slot after each transaction, including rollback. This
seeds storage only: it does not fabricate creator nonce, balance or code, model
external account effects, admit CREATE2, or establish full deployment A/B/C
equivalence. Those account inputs, complete gas/memory integration and the
remaining source-admission obligations still have to be implemented.

Stateful differential implementation snapshots bind the recorded Git HEAD to the campaign workspace and recheck it during replay. A commit switch with byte-identical sources still invalidates the campaign; an unavailable Git revision is an instrumentation error. This supplements source/artifact identity checks and does not certify unexecuted test phases.

### Regression evidence: `unchecked` blocks and tuple destructuring

`UncheckedSequence` and `TupleSequence` add stateful A/B/C fixtures for already
supported constructs: narrow `uint8`/`uint64` wrapping, unchecked mapping
decrements, `require` inside unchecked helper blocks, checked helpers called
from unchecked code, elided tuple components, conditional tuple selection,
literal tuple declarations, and multi-value root returns. An `unchecked` block
in a value helper may now contain a returning `if` when the block has no
block-level declarations: its statements are lowered into the helper
continuation followed by a synthetic block-end marker that restores checked
arithmetic, and each `if` branch restores the lexical `unchecked` flag. Plain
helper blocks with partial returns and such unchecked blocks with declarations
still reject with located diagnostics. Each fixture has
metamorphic source variants (`check_storage --fixture unchecked-blocks` /
`tuple-destructuring`) and scheduled importer mutants
(`import-unchecked-block-*`, `import-tuple-destructuring-*`). Literal tuples on
the right of tuple assignments are supported when their components satisfy the evaluation-order checks.

Whole-contract frame proofs can use `Transactions.AdversarialEntryPointSequence` and `invariant_of_adversarial_entry_points` to vary both the transaction context and permitted oracle at each public call. Every permitted oracle must satisfy the actual per-entry-point execution obligation. The rule includes observed reverting frames through rollback; ABI decoding, dispatch and value transfers remain separate obligations. `adversarial_sequence_append` composes observed prefixes.


## Legacy recovery and byte-signature validation

The explicit 0.7.6 profile admits the resolved global
`ecrecover(bytes32,uint8,bytes32,bytes32)` builtin. Conversion to `uint8` takes
place before encoding. A closed byte transport calls precompile address 1,
reserves a zeroed output word and uses the legacy compiler's scratch layout.
Invalid signatures can return no bytes, leaving the zero address. This does not
impose a low-`s` policy: valid high-`s` signatures remain valid for the precompile.
See the [versioned Solidity documentation](https://docs.soliditylang.org/en/v0.7.6/units-and-global-variables.html#mathematical-and-cryptographic-functions).

A resolved `view` interface or abstract virtual function with signature
`(bytes32, bytes memory) returns (bytes4)` is admitted through an explicit
contract conversion of an address. The selector is derived from the declaration;
no method name, magic value or benchmark contract is hard-coded. This includes
the [ERC-1271 method](https://eips.ethereum.org/EIPS/eip-1271).
The transport ABI-encodes the complete buffer, checks code existence, uses
`STATICCALL`, forwards a failed child's exact bytes, rejects successful responses
shorter than one ABI word, and cleans the trailing 28 bytes of the returned word
as ABI coder v1 does. Extra return bytes are ignored. The source chooses how to
compare the result and what error to raise. Argument assignments and nested
stateful calls remain rejected because their evaluation order needs separate
support. Empty-code and precompile targets fail the legacy code-existence check.

Both transports use an explicitly supplied byte-call environment in Denote.
Absent instrumentation or requests outside that environment's domain are errors,
not evidence of a Solidity revert. The model does not prove secp256k1 recovery or
assume that an arbitrary validator authorizes correctly. Compilation transport
proof status remains `assumed`; dispatch equations and coverage are checked, but
they are not a proof of Yul or Solidity equivalence. Gas equivalence is excluded.

`check_legacy_signature_calls` compares source EVM, Denote, and compiled-model EVM
with independent `eth-keys` recovery calculations. Cases include valid low/high-s
signatures, zero/out-of-range scalars, invalid v, uint8 truncation, repeated
recovery with an invalid second signature, memory-layout observation, calldata
hashing, dirty/short/long bytes4 responses, exact reverts and short-circuiting.
Run each storage-declaration context in its own source compilation:

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_signature_calls \
  --context 0 --output .lake/legacy-signature-calls
# Also run --context 1, --context 2 and --optimized in fresh output directories.
python3 scripts/solidity_import_mutations.py --jobs 2 \
  --task ecm-legacy-recovery-stale --task ecm-legacy-validator-selector \
  --task ecm-legacy-code-existence
```

This slice alone does not import a complete multisignature authorization path.
Dynamic byte construction beyond static scalar hashing, general external signatures,
and ABI-v2 byte decoding remain outside the legacy boundary. Full downstream integration,
authorization proofs and duplicate-signature mutation checks remain separate work.


## Legacy bytes-memory pointer reconstruction

The explicit 0.7.6 profile admits uninitialized `bytes memory` locals (the
zero-slot header at `0x60`), aliases, high-level pointer reassignment and resolved
assembly assignments such as `viewData := add(add(data, offset), 32)`. Assignment
copies an address, performs no memory access and does not allocate or copy a
buffer. Addresses wrap modulo `2^256`. Rebinding a local or helper parameter does
not rebind its aliases or caller parameter.

Descriptors retain a data pointer; `.length` reloads the physical header at
`pointer - 32` each time. Bytes-rooted assembly reads admit nested arithmetic,
unaligned addresses and reads into adjacent memory. Every legacy entry includes
the Solidity free-memory prologue, including entries without bytes parameters.
No application bounds check is inserted: callers must validate untrusted offsets
and lengths before consuming a reconstructed buffer.

The legacy bytes4 transport takes the target, hash and data pointer. It stores
the selector and static arguments before loading the length, then copies payload
words in forward order. A header overlapping the call scratch area sees those
stores; an overlapping copy sees previous copy writes. This preserves the
legacy encoder's ordering instead of snapshotting a logical slice in advance.
Existing aliases also observe scratch changes made by recovery calls.

`LegacyBytePointers.sol` and its differential runner cover default and arbitrary
pointers, wrapped/unaligned offsets, root and helper rebinding, branch and loop
assignments, live alias lengths, overlapping validator encoding, checked embedded
buffers and exact error payloads. An independent byte-array oracle checks all
three routes. Run storage contexts 0, 1 and 2 with both optimizer profiles:

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_byte_pointers \
  --context 0 --output .lake/legacy-byte-pointers
python3 scripts/solidity_import_mutations.py --jobs 4 \
  --task import-legacy-bytes-header --task import-legacy-pointer-zero-slot \
  --task import-legacy-pointer-length --task import-legacy-pointer-encode-order
```

These are finite functional checks, not universal compiler correspondence or
application authorization proofs. Memory reads/copies remain within a finite
resource domain; gas, out-of-gas and huge allocations are not modeled. Pointer
assignment itself is tested even for huge addresses because it does not read
memory. General continuing memory writes, byte allocation, byte indexing,
dynamic byte returns, ABI-v2 byte decoding and assembly control flow remain
rejected. The transports retain `assumed` proof status; no new axiom is introduced.


## Legacy static ABI hashing

The explicit 0.7.6 profile admits `keccak256(abi.encode(...))` at ABI-coder-v1
call sites. Arguments are unsigned integers, addresses/contracts, booleans and
fixed bytes, including typed conversions and nonnegative integer literals.
The resolved `this` builtin supplies the current contract address directly.
Scalar identifiers/member reads are allowed; nested calls, arithmetic and
assignments in argument trees remain rejected. The read-only assembly slice
also admits zero-argument `chainid()` through the existing environment expression.

`LegacyAbi.lower` writes one 32-byte word per argument, cleans narrow words,
stores a byte-length header and advances the free pointer by header plus payload.
Fixed bytes are left-aligned; other admitted scalars are right-aligned. The
allocation starts at the current free pointer even when an earlier packed
encoding left it unaligned. Empty tuples allocate only their 32-byte header.
This follows the [pinned 0.7.6 encoder](https://github.com/ethereum/solidity/blob/v0.7.6/libsolidity/codegen/ExpressionCompiler.cpp)
and [ABI encoding rules](https://docs.soliditylang.org/en/v0.7.6/abi-spec.html#formal-specification-of-the-encoding).

`check_legacy_static_abi` compares source EVM, Denote and generated EVM against
independent `eth_abi`/Keccak bytes and physical-memory observations. Cases cover
dirty calldata scalars, truncated/trailing heads, constants, contract identity,
chain ID, inlined helpers, loops and packed-to-standard allocation composition.
`check_legacy_packed_rejections` retains the formerly rejected standard encoding
as a mandatory positive import control and checks both encoding families'
unsupported boundaries. The `import-legacy-static-*` compiler mutations target
header size, word stride, allocation alignment and chain ID; tool failures do
not count as detections.

This does not admit dynamic ABI encoding, allocated local/returned byte buffers,
enums, calldata-copying assembly, raw narrow assembly reads or general memory
hashing. ABI-v2 encoding sites still reject, including reached helpers. Finite
execution evidence does not prove frontend equivalence or cryptographic security;
gas/resource exhaustion remains outside the model.

## Legacy static packed hashing

The explicit 0.7.6 profile admits `keccak256(abi.encodePacked(...))` at ABI-coder-v1
sites, with literal strings/hex bytes, unsigned integers, addresses, booleans and
fixed bytes. Arguments may be scalar identifiers, member reads or conversions;
helper calls, nested hashes, arithmetic and assignments inside the packed argument
list remain rejected. Compute such values in prior statements. The source unit
containing the encoding determines the ABI-coder restriction, including helpers.

This path writes the payload directly at `mload(64) + 32`. It then writes its
length header and advances the free-memory pointer to the exact end, without
word rounding. Literal chunks and cleaned scalar values use overlapping 32-byte
stores, retaining their trailing writes and pre-existing memory beyond them.
Empty encodings allocate a length word. Hashes in subsequent statements and loops
observe the resulting, possibly unaligned, pointer. The modern encoder is unchanged.

`check_legacy_packed_hash` compares source EVM, Denote and generated EVM with
independent packed-byte hashes, physical-memory expectations and recovery vectors.
It covers scalar widths, empty/multibyte/long literals, decoder allocations,
unaligned memory observation, repeated hashing, loops and precompile scratch
memory. `check_legacy_packed_rejections` checks the located rejection boundary.
The `import-legacy-packed-*` mutations target allocation rounding, length headers
and scalar alignment. These are finite functional checks, not a proof of source
correspondence or cryptographic correctness; gas/resource exhaustion is excluded.

Dynamic packed arguments, direct hashing of arbitrary buffers, packed buffers as
helper arguments or local initializers/returns and ABI-v2 packed encoding need separate semantics and
evidence. This extension does not establish application authorization properties.


## Ordered signature authorization

The experimental 0.7.6 profile can compose bounded loops, guarded arithmetic,
record decoding, bytes-memory reconstruction, recovery, bytes4 static validators,
and packed hashing in a thresholded ordered-record checker. The generic fixture
`LegacyOrderedSignatures.sol` combines four modes: raw recovery, prefixed recovery,
executor/preapproved hashes, and contract validation. Existing admission limits
for each constituent construct still apply.

`Compiler.SolidityImport.OrderedEntryPoint.entry_authorized` proves a property of
actual `Denote.execStmtList` execution. A successful complete entrypoint yields an
actual loop trace containing exactly the requested number of distinct signers.
Every signer has nonzero membership in the **initial storage snapshot**, is
nonzero, and differs from the designated sentinel. `EntryEvidence` records the
reached count read and trace; distinctness is a conclusion, not an assumption.
For a stored-threshold wrapper, `evidence_stored_count` and `evidence_positive`
connect that count to initial storage and establish positivity from the reached
zero-rejection gate. A zero-count explicit helper can still succeed with no signers.

The proof is decomposed into legacy static-call storage/local frames, a closed
read-only statement fragment, the lowered short-circuit guard, loop induction,
and complete-entrypoint composition. Certificates exclude early successful exits
and changes to protected locals/storage. Static child frames follow from the
existing checked adversary boundary. The smoke proof
`LegacyOrderedSignaturesProofs.lean` instantiates these certificates on an actual
Solidity import and proves kernel equality with its **entire** imported body.
No source/model/compiler semantics are replaced and no new axioms are introduced.

This establishes resolved-signer authorization in the imported interpreter. It
does not prove secp256k1 unforgeability, the correctness of arbitrary external
validators, linked-list reachability, configuration invariants, transaction
execution, delegatecall behavior, or gas/resource adequacy. The executor argument
is an explicit input; its relationship to a transaction caller is outside this
checker. Solidity-to-model and model-to-EVM correspondence remain experimentally
validated boundaries, not consequences of the authorization theorem.

The independent Python oracle decodes raw records, uses native Python secp256k1
recovery, and checks an explicit initial membership/approval world. Contract mocks
bind responses to complete ABI calldata. Every transaction has an exact return or
revert-payload expectation, compared against source EVM, Denote, and compiled EVM.
Cases cover all four modes together, stored thresholds, zero counts, truncation,
ignored tails, ordering, duplicate signers across modes, nonmembers, distinguished
addresses, high-s signatures, dirty words, dynamic offsets, checked arithmetic,
and malformed/failed contract responses. Shifted storage slots and optimization
can be exercised with the same oracle:

```bash
turbo-lean build Contracts.SolidityImportSmoke.LegacyOrderedSignaturesProofs --project-dir .
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_ordered_signatures \
  --output .lake/ordered-signatures
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_ordered_signatures \
  --optimized --context 2 --output .lake/ordered-signatures-optimized
PYTHONPATH=scripts python3 -m solidity_differential.check_ordered_signature_mutation \
  --output .lake/ordered-signature-mutation
```

The mutation changes the source rejection guard from `current <= previous` to
`current < previous`. It requires an unchanged positive control to pass first,
then requires duplicate acceptance to violate the independent oracle on **all
three routes**, in both the explicit-count and stored-threshold entrypoints,
with no inter-route divergence. This is a source/property mutation:
three agreeing implementations can all execute the same authorization bug.
Compilation errors, missing oracle rows, and instrumentation failures never count
as detections. Zero-address acceptance is recorded separately and cannot substitute
for a duplicate witness. The campaign is also registered as the
`ordered-signature-duplicate` task in `scripts/solidity_import_mutations.py`.
Generated campaign JSON, Yul and proof/build artifacts stay under ignored `.lake/`.


### Legacy raw CALL and DELEGATECALL (experimental)

The explicit 0.7.6 profile admits whole Yul assignment/declaration values
`call(gas, target, value, offset, size, 0, 0)` and
`delegatecall(gas, target, offset, size, 0, 0)`. Operands must be effect-free;
the output memory region must be literally `(0, 0)`. The target is truncated to
160 bits by the opcode. A direct address-typed helper operand is consequently
safe here; this does not permit other dirty narrow assembly reads. Success is
an explicit boolean, without a code-existence check or automatic failure bubbling.

Enum inputs may pass to resolved internal helpers. Six scalar comparisons check
the member bound at use and execute INVALID on invalid ordinals. ABI-v1 entry
still cleans to uint8 without checking the member bound. Enum storage, locals,
helper returns, external enum arguments and assembly assignments remain rejected.

The closed `SolidityRawCall` transport reads exact physical input bytes. `RawCalls`
debits and credits CALL value before the child; insufficient funds return false
with an empty buffer. DELEGATECALL transfers nothing and inherits the parent's
address, sender and value. An explicit external environment supplies child
execution. Failed children restore the entry world while retaining accesses and
revert bytes; exceptional children leave an empty buffer. Successful children
commit persistent effects while restoring parent context and memory.

`returndatasize()` reads the latest complete byte buffer. The exact terminal
block `let p := mload(64); returndatacopy(p,0,returndatasize());
revert(p,returndatasize())` forwards those bytes. Other return-data copies and
nonempty output areas remain rejected. Raw calls require a trailing continuation:
local computations, checks, scalar events with storage-free arguments, further
closed calls, and returns/reverts are allowed. Later persistent/transient storage
reads and writes remain rejected, including inside branches and event arguments.
The checked continuation justifies the compiler's CEI/reentrancy opt-outs;
it does not assume that a delegated or reentrant child leaves caller state intact.

`check_legacy_raw_calls.py` compares original 0.7.6 bytecode, executable Denote,
and emitted Yul on the EVM. An independently specified child program records
calldata hashes, sender/address/value, balance, origin and a persistent counter,
and returns, reverts or halts exceptionally. Independent Python expectations
check every route's bytes, balances and storage. Cases include unaligned payload
lengths, empty accounts, value failures, consecutive calls, outer rollback and
invalid enum ordinals. Five compiler/model mutations and adjacent rejection
controls exercise the boundary. `RawCallProofs` proves universal failure rollback,
delegate context and caller-context restoration; these are model properties,
not a Solidity-to-EVM equivalence theorem.

Gas metering (including memory expansion, stipend and EIP-150 caps), call-depth
limits, arbitrary external bytecode, payable entry, general reentrancy reasoning,
and arbitrary external logs remain outside this raw-call validation. Named payable
entrypoints have the separate zero-fee envelope below. Request gas
is the supplied opcode operand; the external environment must specify how gas
and call depth affect its response. The fixture uses ample fixed gas and emits
no external logs; the post-call log campaign below covers that boundary separately.
Nonzero transaction values require the explicit envelope below.
Semantic references: [EIP-7](https://eips.ethereum.org/EIPS/eip-7),
[EIP-211](https://eips.ethereum.org/EIPS/eip-211), and the
[pinned enum cleanup implementation](https://github.com/ethereum/solidity/blob/v0.7.6/libsolidity/codegen/CompilerUtils.cpp).


### Named payable entrypoints and value transactions (experimental)

Legacy named public/external payable roots preserve `isPayable` through import
and quotation into compiler dispatch. Internal helper calls do not acquire an
external nonpayable guard. Receive/fallback dispatch, payable constructors and
the complete transaction-execution flow remain separate work.

`ValueTransactions.prepare` supplies an explicit **zero-fee EOA envelope**. It
checks a distinct code-free sender, sufficient funds, the 64-bit nonce limit,
coherent recipient balance, and nonwrapping balance credit. It reserves the
sender's next nonce, then debits the sender and credits the executing contract
before ABI decoding or body execution. `msg.value` and `address(this).balance`
therefore include the incoming value. The prepared balance is available to raw
CALL, and DELEGATECALL inherits the nonzero value without a second transfer.

`settle` preserves success effects. Nonpayable rejection, ABI failure, explicit
REVERT and INVALID restore the complete pre-transfer world, retaining the
reserved sender nonce. Child failure alone does not revert the incoming payment;
an outer revert rolls back both that payment and all child effects. Envelope
admission failure is an instrumentation error, not a fabricated Solidity revert.
`denotePrepared` adds the external payability check around public function
Denote. `denoteFunction` and `Transactions.executeBody` retain their documented
body/frame semantics and do not silently debit an unprovided sender world.

The JSON runner opts in with `valueTransactions: true`; the Python Denote adapter
uses `value_transactions=True`. Replay supplies explicit balances and account
nonces. The EVM adapter's `zero_fee=True` mode sets the next block's base fee and
transaction gas price to zero and checks the actual receipt. Sender balances and
nonces are compared exactly, without subtracting gas charges from observations.
The default call-frame mode still rejects nonzero value.

`check_legacy_payable.py` checks stateful and stateless contracts against original
0.7.6 EVM bytecode, executable Denote and generated EVM bytecode. Independent
Python expectations cover complete return/revert bytes, balances, nonces,
storage, logs, truncated ABI words, helper value inheritance, incoming funds
spent by CALL, delegate context, child failure and outer rollback. Six actual
mutations target credit, debit, rollback, nonce persistence, payability guarding
and payable metadata. Former payable rejection controls now require admission;
`check_legacy_payable_rejections.py` checks invalid envelopes separately.

`ValueTransactionProofs` proves model-level balance conservation at preparation,
nonce reservation, external nonpayable guarding, and success/failure settlement.
It does not prove source/importer/compiler equivalence, gas/resource adequacy,
transaction signature validity, fee accounting or arbitrary external programs.
The envelope excludes EIP-7702 sender code and assumes the supplied EOA sender is
authorized; it is not a full Ethereum transaction-validity model.

References: [Solidity 0.7.6 contract semantics](https://docs.soliditylang.org/en/v0.7.6/contracts.html),
[EIP-2681 nonce limits](https://eips.ethereum.org/EIPS/eip-2681), and the
[code-free sender rule](https://eips.ethereum.org/EIPS/eip-3607).


### Post-call events and exact child-log rollback (experimental)

Trailing-call continuations admit scalar `emit` statements whose arguments read
no persistent or transient storage. This supports events derived from captured
locals, call success and return-data size. Existing storage-access and interaction
restrictions remain in force, including inside event arguments and branches.
Dynamic/anonymous source events and arbitrary post-call assembly are not added.

`Verity.EncodedLog` records the execution address, zero to four topics, and exact
payload bytes. `Event.rawLog` carries that observation in the ordered event
journal; existing typed events retain their ABI argument view. The sequence runner
encodes root typed events with the root ABI and address, but consumes complete
external logs directly: a child need not share the caller's event declarations.
The closed memory-log transport also records exact bytes and its executing address;
its existing word-aligned source-admission restriction is unchanged.
`DenoteResult.eventTrace` exposes the complete ordered records. The old `events`
field remains a word-only compatibility view, not a complete EVM log encoding.

Successful raw calls must preserve the entire prior journal and append only
complete logs with at most four topics. Malformed extensions are instrumentation
errors. Child REVERT/INVALID drops the child's logs while retaining caller and
successful sibling logs. A later outer REVERT/INVALID restores the transaction's
entry journal and account state, including value transfers; the reserved EOA nonce
still advances. DELEGATECALL logs use the execution account's address.

`check_legacy_post_call_events.py` compares original Solidity 0.7.6 EVM execution,
public/traced Denote and generated EVM execution against independent Python
expectations. Its 385 cases cover LOG0 through LOG4, empty/odd payloads, nested
CALL/DELEGATECALL, failed children, consecutive calls, pre/post-call events,
full-buffer revert forwarding, late INVALID, dirty enums and incoming/outgoing
value. Both compiler optimization settings are exercised. The explicitly bounded
`PostCallLogMocks` program and separately compiled `PostCallLogOracle.sol` supply
the child behavior; neither is a general external-bytecode interpreter.

Six executable mutations target emitter, payload, ordering, pre-call prefix,
caller events and outer rollback. A mutation counts only after an unmodified
control passes and the changed executable produces runtime divergence. Nine
boundary controls reject malformed external journals and check failure buffers.
`EventLogProofs` supplies eight kernel-checked model laws for append/order,
account preservation, prefix admission and child/outer transaction rollback.
These laws do not establish Solidity/importer/compiler correspondence. Gas,
call-depth adequacy, arbitrary external programs, callbacks, and complete
application execution remain explicit obligations or later work.


### ABI-v1 void callbacks and constant-slot address reads (experimental)

Solidity 0.7.6 admits resolved, nonpayable interface calls with no return values.
Receivers must be explicit interface conversions of effect-free address expressions.
Arguments are captured `uint256`, `bytes32`, address/payable-address, bool or enum
scalars and existing memory/calldata bytes. Enum ordinals retain the legacy INVALID
use-site check. Dynamic arrays, structs, strings, value-bearing typed calls,
effectful argument evaluation remain rejected. Internal calldata forwarding and
calldata-to-memory helper conversions use the separate legacy helper slice below. The call site must use ABI coder v1.

`LegacyVoidCall` is a closed, assumed transport. It writes the selector and all
scalar head words before dynamic offsets and payloads, at the current free pointer.
Memory lengths are read during encoding and reloaded for the copy after the outgoing
length store; overlapping copies observe earlier writes. Calldata arguments copy
exact source bytes with zero padding, including when the external interface declares
its bytes parameters as memory. This external ABI conversion allocates no separate
intermediate memory buffer in the pinned compiler. The free pointer is not advanced. Code must
exist at the cleaned target address. CALL sends zero value and has no output area:
success ignores arbitrary return bytes, including empty/noncanonical buffers.
Failure forwards the complete revert buffer. Exact returndata remains observable.

Constant-slot assembly `sload` is also admitted. Address results are cleaned to
160 bits at the Solidity boundary; later unmasked narrow assembly reads remain
rejected. Dynamic-slot reads remain rejected. Constant-slot writes are described below. This permits
reading a callback address from a fixed storage slot before entering the interaction
window. After the first callback, continuations still require storage-free
expressions and admit only the existing closed calls, scalar events and termination
forms. Reading storage after a callback, including in another callback's arguments,
remains rejected.

`check_legacy_void_callbacks` compares original 0.7.6 EVM execution, public/traced
Denote and generated EVM code against independent ABI, storage, balance, nonce and
log expectations. It covers both callback phases, full eleven-argument tuples with
two byte buffers, empty/odd buffers, pointer aliases, dirty stored addresses, arbitrary
successful return lengths, pre/post rejection, raw CALL/DELEGATECALL and outer rollback.
The separately compiled `VoidCallOracle` and finite `VoidCallMocks` program supply
external behavior; they are not a general external-bytecode interpreter.

Focused controls reject malformed closed metadata, missing environments and adjacent
unsupported source forms. Actual runtime mutants target offsets, code checks,
failure forwarding, omitted phases, accidental return decoding, address cleanup and
head-store order, each after an unchanged control. Compiler/build failure is never
a mutation kill. The kernel-checked coverage equation pins the canonical dispatch
arm; the existing raw-call and event-journal laws supply model rollback properties.
These are not Solidity/importer/compiler correspondence proofs. Gas, memory-resource
and call-depth adequacy and arbitrary callback implementation correspondence remain
explicit external-environment obligations. Complete application execution and refund accounting require additional work.
Callback installation uses the separately described static-query/storage slice below.


### ABI-v1 bool static calls and constant-slot stores (experimental)

Solidity 0.7.6 admits resolved view/pure interface calls returning one bool. The
call site must use ABI coder v1, an explicit interface conversion of an address,
and effect-free receiver/argument expressions. Argument types are exact declared
`uint256`, address/payable-address, bool or fixed bytes. Fixed bytes are left aligned
and truncated to their declared width; narrow fixed-byte root ABI remains rejected.
Resolved `type(I).interfaceId` uses only the interface's own selectors, excluding
inherited functions. Other `type` builtins are not admitted by this extension.

The closed `LegacyBoolCall` transport captures operands before encoding at the
current free pointer. It requires code at the cleaned target address, uses STATICCALL
with a 32-byte output area, forwards failed-call bytes exactly, and rejects successful
responses shorter than 32 bytes. ABI-v1 bool decoding treats every nonzero word as
true. Only the decoded binding is cleaned: physical memory preserves the raw response
word and the free pointer is unchanged. Extra response bytes remain in returndata.
A successful static call permits subsequent caller storage operations; it does not
relax the storage-free continuation restriction after state-changing callbacks.

Assembly blocks consisting only of `sstore` statements accept literal/identifier
operands with a resolved constant slot and existing safe scalar reads. Full words
and cleaned external address arguments are supported. Dynamic slots, compound value
expressions, assembly loops and untracked narrow values in internal helpers remain
rejected. The existing dirty-narrow-assembly-read rejection also remains in force.

`check_legacy_static_installation` compares original Solidity EVM, public/traced
Denote and generated EVM against independent state, ABI, event, balance and nonce
expectations. Cases include inherited interface IDs, false/noncanonical true words,
short/long responses, repeated queries preserving separate results, exact revert
bytes, static write attempts, empty code (including
precompiles), dirty address/bool/fixed-byte inputs, installation/replacement/disabling,
authorization rejection and rollback after a later revert. The finite external
`StaticBoolOracle` is independently compiled and modeled by `StaticBoolMocks`.
Model boundary checks reject malformed metadata and missing instrumentation. Runtime
mutants alter code checks, truth decoding, short-response rejection, failure bytes,
selector encoding, call kind, free-pointer behavior and the stored slot; each must
first pass an unchanged control.

Self-authorized entrypoints are tested using an explicit `selfCallExperiment` mode
mirroring Anvil impersonation. It permits only zero-value self calls, advances the
synthetic envelope nonce and retains rollback behavior. Ordinary transaction mode
still requires a distinct, code-free EOA. This experiment supplies an inner call
context; it does not establish that a full application transaction can reach it.

The transport remains assumed. The kernel-checked canonical dispatch equation is
a model law, not Solidity/importer/compiler equivalence. External-program
correspondence and adequate gas, memory resources and call depth remain obligations;
full application execution and refund accounting are not established by this slice.


### Internal calldata forwarding and memory helper arguments (experimental)

Solidity 0.7.6 ABI-v1 calls may pass an existing `bytes calldata` identifier to a
resolved internal call, including direct library calls and public functions called
internally. A calldata parameter retains the original offset and length; forwarding
through multiple helpers does not allocate memory or change the free pointer.

Passing the same region to a `bytes memory` parameter allocates a fresh length
header and payload at the current free pointer. The pointer advances by 32 plus
the payload length rounded up to 32 bytes, before the copy and helper body. Every
conversion allocates independently, including empty regions and unused parameters.
The copy preserves the exact payload and writes a zero word immediately after its
end, clearing dirty padding and the following 32 bytes. Memory arguments already
in memory retain the existing pointer/alias behavior and live length reads.

`LegacyMemory.materializeBytes` uses existing model memory and loop statements;
there is no new external-call transport or axiom. Source admission remains narrow:
slices, returned calldata, reassignment, element reads, dynamic construction and
ABI-v2 byte roots/call sites remain outside this slice. Effectful argument ordering,
post-interaction storage access and external-call restrictions are unchanged.

`check_legacy_calldata_helpers` compares original 0.7.6 EVM, public/traced Denote
and generated EVM against an independent byte-addressed memory oracle. It checks
allocation order, repeated and unused parameters, aliases, mixed memory/calldata
arguments, dirty padding, truncated/noncanonical ABI and conditional calls.
`check_legacy_calldata_execution` exercises forwarded arguments reaching existing
CALL/DELEGATECALL helpers, exact return buffers, value transfers and outer rollback.
Adjacent source controls retain explicit rejection; executable mutants alter the
source offset, length header, allocation rounding/reuse, padding and forwarding.
Each mutant must first pass its unchanged control and then diverge at runtime.

This is finite semantic evidence, not a Solidity/importer/compiler equivalence
proof. Gas, memory resources and call-depth adequacy remain assumptions. Complete
application execution, argument side-effect ordering, gas observations and refund
handling still require additional work. Generated artifacts remain under `.lake/`.


### Scalar conditional expressions (experimental)

Solidity 0.7.6 admits `condition ? yes : no` for unsigned integers, bools,
addresses (including payable/contract addresses), and fixed bytes. Nested choices,
scalar helper results/arguments, selected scalar assignments and existing increment
forms use the shared scalar lowerer. The condition is evaluated once; the chosen
arm's prelude and value stay inside its `Stmt.ite` branch. Skipped arms do not
allocate, emit events, write storage or execute their require/revert behavior.
Legacy wrapping arithmetic and ABI-v1 scalar cleaning retain their existing rules.
Narrow fixed-byte root parameters/returns remain rejected; internal conditional
values can be observed through the existing full-word conversions.

The declaration gate validates both arms, including statically unselected arms.
Signed values, enum results, tuples, dynamic/reference values and function pointers
remain outside this legacy conditional slice. Existing restrictions on argument
ordering and storage access after external interactions still apply. This does not
admit `gasleft()`, gas prices, refund calls or general effectful call arguments.

Division-path validation follows each conditional edge using the same conservative
facts as `if` and short-circuit expressions. For example, `d == 0 ? 0 : n / d`
is admitted for an unsigned, never-assigned local `d`. Facts do not escape the
expression, cross helper calls, survive mutation, or justify a truncated divisor.
An unguarded zero-divisor path remains rejected; no legacy exceptional-halt behavior
is replaced with a modern panic.

`check_legacy_scalar_conditionals` compares the original compiler, public/traced
Denote and generated EVM with independent ABI, arithmetic, allocation, state and
ordered-event expectations. It covers both branch outcomes, nested choices, dirty
ABI values, width/overflow boundaries, lazy failures/copies, condition effects,
selected increments/assignments and outer rollback. `check_legacy_conditional_rejections`
checks supported scalar contexts and neighboring unsafe division/non-scalar cases.
Executable mutations invert the choice, eagerly execute either arm or repeat the
condition; an unchanged control must pass before runtime divergence counts.

These are finite translation checks, not a new compiler-correctness theorem.
The existing model primitives and resource/external-world assumptions are unchanged.


### Independent postfix helper arguments (experimental)

The 0.7.6 profile admits one direct unsigned `x++` argument in an internal call
with multiple arguments. The target must be a writable scalar local/parameter or
a scalar storage identifier. The existing lowering captures its old value, writes
the incremented value once (with legacy width-dependent wrapping), and passes the
old value to the helper. The helper observes the updated storage; outer failure
rolls back the increment, helper writes and logs under the existing transaction model.
Scalar, multiple-result and void helpers share the argument boundary.

[Solidity leaves sibling evaluation order unspecified](https://docs.soliditylang.org/en/v0.7.6/control-structures.html#order-of-evaluation-of-expressions).
This slice admits only
commuting siblings: numeric/bool literals, distinct scalar identifiers and at most
one existing calldata bytes identifier. That descriptor may be forwarded or
copied for a memory parameter; its allocation cannot alias the incremented scalar.
The existing finite-resource assumptions still apply. A sibling read of the target,
multiple increments, prefix/decrement/assignment forms, computed expressions,
sibling calls, memory/storage references and multiple byte descriptors remain
rejected in this new multi-argument boundary. Modern compiler admission is unchanged.
Single-argument calls retain their previous boundary.

`check_legacy_postincrement_arguments` compares original 0.7.6 EVM, public/traced
Denote and generated EVM with independent old/new-value, state, event, ABI and
rollback expectations, including every argument position, local/helper aliases,
narrow locals, wraparound, nested calls and calldata forwarding/copying.
`check_legacy_postincrement_rejections` checks the neighboring rejection boundary.
Executable mutations pass the new value, write twice, omit the write or pass the
new local value; each must compile and fail runtime checks after a passing control.
No new primitive, axiom, transport or source-equivalence theorem is introduced.


### Immutable scalar forwarding into assembly (experimental)

The 0.7.6 profile preserves the ABI decoder's clean-width information through
internal helper calls when an argument is a direct, immutable scalar parameter
identifier and the parameter has the same source type (or both are address,
payable-address or contract types). Nested scalar, tuple and void helpers can
therefore read these values in assembly, including scratch-memory hashing.
The information is scoped to each invocation and restored on return. A parameter
written anywhere in the declaration, including modifier arguments, is excluded.

This tracks the assembly word, not merely the high-level Solidity value.
[Solidity 0.7.6 warns that narrow values may retain dirty bits in assembly](https://docs.soliditylang.org/en/v0.7.6/assembly.html#access-to-external-variables-functions-and-libraries).
External ABI-v1 address words are masked to 160 bits and enum words to eight bits.
Enum words outside the declared member range remain observable in assembly;
converting an enum to an integer retains the existing use-site `INVALID` check.
Internal forwarding does not introduce a new enum range check. The pinned
[compiler's conversion logic](https://github.com/ethereum/solidity/blob/v0.7.6/libsolidity/codegen/CompilerUtils.cpp)
distinguishes conversion from forced cleanup.

Casts, computed expressions, local copies without tracked provenance and modified
parameters still fail the raw narrow assembly-read gate. Bound `using for`
receivers remain excluded from this new propagation because their cleanup rules
differ from ordinary positional arguments. Existing full-word, literal and
explicitly masked-address paths retain their boundaries. Modern admission is
unchanged.

`check_legacy_helper_assembly_scalars` compares source EVM, public/traced Denote
and generated EVM against independent raw-word, hash, event, nonce and rollback
expectations. It includes dirty ABI inputs, enum boundaries, nested and repeated
calls, payable-address forwarding and optimizer on/off. The adjacent
`check_legacy_helper_scalar_rejections` checks unknown provenance and writes,
including a clean call followed by a dirty call to the same helper. Executable
mutations corrupt the forwarded address or enum word, or add an incorrect early
enum range check; each requires a passing control and runtime divergence.
These are finite translation checks; no new primitive, axiom or source-equivalence
theorem is introduced. Gas-sensitive execution remains outside this slice.


## Original-bytecode gas observations (experimental, Solidity 0.7.6)

Set `sourceGas := true` with the explicit pinned 0.7.6 profile to import
`gasleft()` and Yul `gas()` as ordered source-execution observations. The default
remains off. This mode verifies gas-sensitive behavior against the **original
solc bytecode**. Compilation of these observations is rejected: regenerated Yul
has different instruction costs and no gas equivalence theorem is claimed.

Each transaction supplies `sourceGas` evidence containing its initial frame gas,
ordered GAS sites, raw CALL/DELEGATECALL boundaries and final instruction span.
`SourceGasRunner` requires complete consumption, including on REVERT. Missing,
reordered, mismatched or unaffordable evidence is an instrumentation error. A
source span includes dispatcher, stack, memory and storage work in the original
bytecode; its cost is never estimated from source statements. Source sites use
solc AST/source-map locations and participate in the import profile digest.

`CallGas` independently calculates the GAS opcode's two-gas charge, input/output
memory expansion, warm/cold target access, value and new-account costs,
EIP-150 cap, value stipend and gas returned from the child. The source call
operand is checked against the functional request; only the derived allowance
is passed to the callee. The callee's success bit and complete returndata must
match the same source observation. Kernel lemmas prove operand bounds, gas
partition, no gas creation on child return, and failure/charging laws. They do
not prove EVM execution or the Solidity frontend.

One gas read may occur alongside independent scalars, existing memory-byte
identifiers, one immutable calldata-byte identifier (forwarded or copied to fresh
memory), and a resolved nonvirtual pure helper with scalar parameters, no
modifiers, and a single call-free return expression. This covers minimum-budget
checks and conditional gas arguments to internal helpers. Multiple gas reads in
unordered siblings, competing effects and other allocation/conversion expressions remain
rejected. The calldata copy and evidence read affect disjoint model state; actual
copy costs and evaluation position come from the original-bytecode meter.

The current source adapter validates complete root CALL/DELEGATECALL traces on
Osaka, exact deployed runtime, source-map sites, actual child allowances and
parent continuation gas. Fixed child programs are independently modeled;
target balances/code and caller storage are compared through successful and
reverting transactions. The EVM and trace adapter are **trusted meters** for
ordinary instruction spans, call context and child gas consumption. The JSON
parser alone does not authenticate provenance. A downstream proof must assume or
separately establish that its evidence describes the intended bytecode, input,
fork and prestate, and that its callee model describes the deployed child.

Typed calls with return values, static transports (including signature precompiles), CREATE2,
nested account access/warmth journals, access-list transactions, EIP-7702 trace
reconstruction, root OOG, and transaction refund/fee accounting are not covered by this adapter. Unmetered
transports fail closed in `SourceGasRunner`; the ordinary functional mode
retains its existing behavior. Frame gas remaining is not receipt gas usage.
The CallGas arithmetic accepts an explicit EIP-7702 delegation-access input,
but that input has no source replay claim here. Full contract execution with
these constructs needs additional adapters and evidence.

Reproduce with the pinned toolchain and Python dependencies:

```sh
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_source_gas --output .lake/source-gas
PYTHONPATH=scripts python3 -m solidity_differential.check_legacy_source_gas --optimized --output .lake/source-gas-opt
PYTHONPATH=scripts python3 -m solidity_differential.check_source_gas_boundaries --output .lake/source-gas-boundaries
PYTHONPATH=scripts python3 -m solidity_differential.check_source_gas_mutations --source-campaign .lake/source-gas --output .lake/source-gas-mutants
```

Both optimizer modes compare source return/revert bytes, observations, balances,
code and rollback. Mutation checks execute altered GAS cost, EIP-150 divisor,
stipend, cold access, parent gas return and ordinary-span charging against saved
actual EVM observations. Each requires an unmodified passing control and an
independently replayed witness; build/instrumentation errors never count.
Campaign artifacts stay under ignored `.lake/`, not in the source tree.

Accounting references: [EIP-150](https://eips.ethereum.org/EIPS/eip-150),
[EIP-2929](https://eips.ethereum.org/EIPS/eip-2929), and
[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702).


### Solidity 0.7.6 native-value and optional-word payments (development)

The importer admits `(bool ok, ) = receiver.call{value: amount}("")` in roots and
inlined scalar/void helpers. Receiver and value must be effect-free scalars; the
only option is `value`, calldata must be an empty literal, and the bytes tuple
component must be discarded. Success is the raw CALL success bit. Failure does
not implicitly bubble returndata or revert: subsequent source checks determine
that behavior. The existing raw-call model checks funds, transfers value before
child execution, commits successful child effects and rolls back failed children.
An outer revert restores the whole frame, including successful earlier payments.

Discarding the bytes result does **not** discard its memory effect. Solc 0.7.6
allocates nonempty returndata at the free pointer, with a length word and rounded
capacity; empty returndata does not advance the pointer. This behavior is lowered
explicitly and tested with return lengths 0, 1, 31, 32, 33 and 64. No code-existence
check is inserted: an explicitly modeled empty account can receive payment.

Static `abi.encodeWithSelector` with a numeric four-byte literal and supported
ABI-v1 scalar arguments constructs selector-prefixed memory bytes. Dynamic
arguments/selectors and ABI-v2 sites remain rejected. Assembly CALL
can additionally copy up to one word into scratch offset zero: exactly
`min(32, returndatasize())` bytes overwrite memory, including on child REVERT.
Other nonempty output regions, including DELEGATECALL outputs, remain rejected.
A scratch-word read requires an immediately following returndata-size case that
establishes at least 32 copied bytes; short and unguarded reads remain rejected. Legacy numeric `switch` cases
lower to one selector evaluation and scoped conditional branches. Immutable Yul
locals retain a proven boolean bound; reassigned/unbounded locals cannot be
assigned to Solidity bools without explicit cleanup.

These constructs preserve source-level optional-word checks. In particular,
empty returndata or an exact 32-byte nonzero word can be accepted without ABI
bool decoding, while short/long returndata, zero words and failed children can
be rejected. The importer neither inserts that policy nor substitutes a strict
`0`/`1` decoder. Post-call memory stores/copies and terminal memory reverts are allowed when their operands
read no storage; the ban on post-call persistent/transient reads/writes remains.

With `sourceGas := true`, the native call's compiler-inserted GAS is identified
by the original call's source site, followed by the existing checked CALL gas
boundary. SequenceRunner accepts an explicit per-transaction `gasPrice` word for
`tx.gasprice` observations (zero when omitted for older fixtures). This does not
add transaction-fee settlement or EVM refund-counter semantics. The payment
campaign normalizes sender fees and envelope nonce before comparing frame state.
Gas-sensitive recompilation remains unavailable; the supported static return layouts
are described below, and other limitations above still apply. Import admission and finite differential
evidence are not full contract verification or a frontend equivalence theorem.

Run the focused campaigns with the pinned environment:

```sh
python3 -m solidity_differential.check_legacy_value_payments --output .lake/value-payments
python3 -m solidity_differential.check_legacy_value_payments --optimized --output .lake/value-payments-opt
python3 -m solidity_differential.check_value_payment_boundaries --output .lake/value-payment-boundaries
```

Each payment campaign includes original-bytecode/Denote comparisons of exact
return/revert bytes, source gas, caller and child storage, balances and rollback,
plus executable model mutants that remove native, asset and outer-failure guards.
Compiler errors or missing instrumentation never count as mutation detections.

The gas-free native fixture also runs original/model/generated-bytecode checks:

```sh
python3 -m solidity_differential.check_native_value_compilation --output .lake/native-value-abc
```

### Memory-only bounded loops after calls (development)

A closed external call may be followed by a bounded `forEach` loop whose body
contains only local bindings/assignments, memory stores, conditionals and nested
loops. `postCallMemoryStmt` and `postCallMemoryList` check this recursively. Every
operand and loop bound must be storage-free and call-free. Storage/transient
writes, calls, gas observations, logs and early exits inside these loops remain
rejected. The existing rules for statements outside loops are unchanged.

This admits the existing Solidity 0.7.6 calldata-to-memory helper conversion
after a callback. It reuses the same physical byte-copy lowering, allocator
advance and tail clearing; it does not hoist a copy across an external call.

`PostCallMemoryFrames` proves the exact admission predicate sound for canonical
Denote execution: all state except local bindings and the two memory views is
preserved. This includes persistent/transient storage, account balances/code,
logs, call observations and source-gas state. Failed evaluations have no successor
state in that frame predicate; transaction rollback is checked separately. The
proof establishes a model frame, not Solidity-frontend or compiled-code equivalence.

The differential fixture composes callback, calldata copy, CALL/DELEGATECALL,
fixed native payment and final callback. Original bytecode, Denote and generated
bytecode are compared on exact return/revert bytes, logs, storage and balances,
including final-callback rollback. The finite callback oracle and gas-free
compilation limits remain explicit. The supported static-call gas adapters are described below; arbitrary return layouts
and complete whole-transaction gas validation remain outside this scope.

```sh
python3 -m solidity_differential.check_post_call_memory_loops --output .lake/post-call-memory
python3 -m solidity_differential.check_post_call_memory_loops --optimized --output .lake/post-call-memory-opt
python3 -m solidity_differential.check_post_call_memory_boundaries --output .lake/post-call-memory-boundaries
```

### Original-bytecode gas for typed callbacks (development)

The explicit 0.7.6 `sourceGas` profile attaches the Solidity call site's source
location to ABI-v1, nonpayable interface calls with no return decoder. This
includes scalar and memory/calldata-byte arguments. The normal profile keeps its
existing explicit gas environment. Metered callbacks cannot be recompiled, even
when their root function has no explicit `gasleft()`.

Encoding and the code-existence check precede the implicit GAS observation.
An empty-code target reverts without consuming a nonexistent GAS/CALL boundary.
Otherwise the same original-bytecode meter checks the GAS charge, source call
operand, EIP-150 allowance, child outcome/returndata and returned gas. The
functional and observing adapters share one execution result. Five kernel lemmas
pin this execution arm and the completion behavior: success installs the consumed
cursor, and failure retains it while forwarding exact revert bytes. Transaction
rollback remains the existing whole-frame operation; remaining frame gas is not
transaction receipt gas or fee accounting.

The generic fixture composes before/after callbacks, bytes, a native payment,
events and an outer failure. It also includes an amount/amount/bytes settlement
callback. Original solc execution and Denote compare gas, exact return/revert
bytes, logs, storage and balances in both optimizer modes. Fixed child runtimes
return/revert their observed entry gas, halt exceptionally, or have no code.
Malformed-evidence controls and executable accounting mutants must fail for their
intended reasons; compiler/instrumentation errors do not count as detections.

The original-bytecode span meter, access/memory context and child gas consumption
remain trusted evidence. The static return/signature layouts described below extend
this profile. Other typed return layouts, arbitrary callback code/reentrancy and nested
account-access journals remain separate work. No full-contract or compiler-equivalence claim is made.

```sh
python3 -m solidity_differential.check_typed_callback_gas --output .lake/typed-callback-gas
python3 -m solidity_differential.check_typed_callback_gas --optimized --output .lake/typed-callback-gas-opt
python3 -m solidity_differential.check_source_gas_mutations --source-campaign .lake/typed-callback-gas --fixture Contracts/SolidityImportSmoke/LegacyTypedCallGas.sol --output .lake/typed-callback-gas-mutants
python3 -m solidity_differential.check_typed_callback_gas_boundaries --output .lake/typed-callback-gas-boundaries
```


### Original-bytecode gas for legacy static calls (development)

The explicit 0.7.6 `sourceGas` profile now covers `ecrecover`, external
`(bytes32,bytes) -> bytes4` validators and scalar-argument external bool predicates.
Each uses a closed `sourceStatic` descriptor with an AST source location. The
ordinary profile retains its existing constructors; both profiles share the exact
legacy memory preparation and return decoder. Short return words revert, dirty
bool words normalize only at the binding, and bytes4 decoding preserves its legacy
padding behavior. Revert payloads are forwarded exactly. These transports are
static: the existing checked byte-call boundary requires world preservation.

The source meter recognizes STATICCALL's six operands, zero value and no stipend.
The original compiler's code-existence check precedes implicit GAS for interface
calls; recovery bypasses that check because precompile 1 has no account code.
The same EIP-150/access/memory boundary calculation checks forwarding and returned
gas. Recovery additionally checks the precompile's fixed 3000-gas cost, including
invalid signatures: an allowance below 3000 fails exceptionally, while invalid
signatures with sufficient gas succeed with empty returndata. This follows
[EIP-214](https://eips.ethereum.org/EIPS/eip-214) and the versioned geth
[precompile implementation](https://github.com/ethereum/go-ethereum/blob/v1.16.5/core/vm/contracts.go)
and [gas constant](https://github.com/ethereum/go-ethereum/blob/v1.16.5/params/protocol_params.go).

`StaticCallGasFrames` proves five model laws for canonical execution and meter
attachment, including exact failure bytes and cursor retention. It does not prove
frontend correspondence, recovery cryptography or an application's authorization
properties. The transport exposes the assumed summary
`legacy_static_original_bytecode_gas_evidence`; original traces, span costs and
access/memory context remain trusted. Ordinary validator gas usage also remains
trace evidence, even when its functional behavior has an independent model.
Gas-sensitive recompilation is rejected.

The generic campaign compares original bytecode and Denote on frame gas, exact
return/revert bytes, events and storage in both optimizer modes. It includes
valid/invalid/high-s recovery, repeated recovery, bytes padding/length boundaries,
dirty bool words, absent code, callee reverts, exceptional static writes and
GAS-observing children. Malformed evidence must reject for the intended reason;
accounting mutants must produce completed numerical mismatches. Isolated EVM
precompile probes at 2999/3000/3001 gas are reported separately: parent out-of-gas
execution is still unsupported and is never counted as a complete frame replay.

Low-level arbitrary STATICCALL, other return layouts, nested access journals,
arbitrary validator correspondence/reentrancy, root out-of-gas and transaction
fees/refund counters remain outside this slice. Application-specific replay and
authorization proofs belong downstream, using pinned source and callee evidence.

```sh
python3 -m solidity_differential.check_static_call_gas --output .lake/static-call-gas
python3 -m solidity_differential.check_static_call_gas --optimized --output .lake/static-call-gas-opt
python3 -m solidity_differential.check_static_call_gas_boundaries --output .lake/static-call-gas-boundaries
```

The registered `static-call-gas-opt0` and `static-call-gas-opt1` mutation tasks also
run the five applicable accounting mutants (GAS cost, EIP-150 cap, warm access,
returned gas and source spans). These typed targets are warm after the code check,
or inherently warm as precompile 1. STATICCALL has no value stipend to mutate.


### Raw legacy STATICCALL and guarded uint256 decoding (development)

Solidity 0.7.6 ABI-v1 tuple initializers of the form
`(bool ok, bytes memory data) = target.staticcall(input)` now preserve the success
flag and complete returndata. The receiver is an address; the input is an existing
memory-bytes local or a static-word `abi.encodeWithSelector` expression. Selectors
may be literals or type-qualified external/public function selectors. Instance
selectors and effectful operands reject; their evaluation is never discarded.
Referenced immutables require explicit deployed bindings, including references
reached through helpers and modifiers. No caller-address substitution is used. Call options, ABI-v2, omitted tuple
bindings and other raw call forms remain outside
this admission path.

The closed `raw_static_call_byte_response` transport has no code-existence check,
no output area and no automatic failure forwarding. Empty-code calls succeed with
empty bytes; a reverting callee produces `false` plus its exact bytes. Nonempty
responses allocate a length header and rounded capacity at the current free pointer,
which may be unaligned. Empty responses use the legacy zero-slot pointer. Allocation
and copying use existing physical-memory statements and retain bytes aliases.

Source checks remain separate statements: a bare `require(ok && data.length >= 32)`
reverts with empty bytes, regardless of the callee's revert payload. Legacy
`abi.decode` is admitted here only for one `uint256` from memory bytes under ABI-v1.
The decoder independently checks for at least 32 bytes and reads the first word;
extra bytes are allowed. Other target types/tuples and calldata decoding reject.

`RawStaticCallFrames` proves six model laws for the checked static-world boundary,
exact response retention, false failure binding, consumed meter and canonical arm.
These laws do not prove importer or bytecode correspondence. Source/model/generated
bytecode campaigns use a calldata-hashing oracle to observe selector and argument
errors, exact empty failures, unaligned allocation, repeated calls, aliases and
minimum-amount checks. Source mutations remove success, decoder-length and minimum
checks; completed counterexamples on all three routes are required.

The optional `sourceGas` profile records implicit GAS at the raw call site and
checks the original STATICCALL boundary. Targets may be cold because there is no
preceding code check; repeated calls test warm access. Both optimizer modes compare
original-bytecode frame gas and functional observations, reject malformed evidence,
and detect six accounting mutations. Source instruction spans, memory/access
context and child gas consumption retain the existing trace-evidence assumptions.
Generated-code gas equivalence is not claimed and metered compilation rejects.

This admits balance-query helpers, not an entire pool or transaction proof.
Arbitrary callee correspondence, nested account-access journals, root out-of-gas,
transaction fees/refunds and general post-state-changing-call composition remain
separate work. The existing post-call admission rules are unchanged.

```sh
python3 -m solidity_differential.check_legacy_static_words --output .lake/static-word-abc
python3 -m solidity_differential.check_legacy_static_words --optimized --context 2 --output .lake/static-word-abc-opt
python3 -m solidity_differential.check_raw_static_mutations --output .lake/static-word-mutants
python3 -m solidity_differential.check_raw_static_gas --output .lake/raw-static-gas
python3 -m solidity_differential.check_raw_static_gas --optimized --output .lake/raw-static-gas-opt
python3 -m solidity_differential.check_raw_static_boundaries --output .lake/raw-static-boundaries
```

The mutation runner registers both optimizer modes, ordinary storage contexts
0/1/2, guard counterexamples and original-bytecode accounting mutants. Runtime
artifacts stay in ignored campaign directories; the generic fixtures and runners
are checked in.


### Explicit deployed immutable bindings (development)

Set `Profile.deployedImmutables := some "deployment.json"` to import scalar immutable
reads and public getters. The path is relative to the Solidity source root. The
JSON object has `version: 1`, a 20-byte `codeAddress`, the complete `runtimeBytecode`
with a `0x` prefix, and a `bindings` array. Each entry contains `source`, `contract`,
`name`, `type` (the exact solc type string), and `word` (a 32-byte hex EVM word).
The source path is its logical standard-JSON name; the contract is the declaring
contract, including for private inherited members. A binding is specific to that
declaration, rather than a potentially shadowed variable name.

The importer compiles the collected sources with its pinned compiler and selected
settings, then checks the submitted runtime against the resulting template and
`evm.deployedBytecode.immutableReferences`. All compiler reference ranges must have
bindings; every occurrence must match, and every byte outside those ranges must
match too, including metadata. Duplicate, foreign, missing, overlapping, out-of-range,
non-word, incorrectly typed and noncanonical bindings reject. Unresolved link
placeholders reject. Declarations optimized out of the runtime cannot be supplied
with invented values; reading one without a runtime reference still rejects.
Sources that cannot produce runtime bytecode with the selected settings reject.

Patch words are right-aligned for addresses and unsigned integers and left-aligned
for fixed bytes; booleans must be zero or one. Signed patches may contain either
a zero-extended narrow bit pattern or its sign extension. The checker compares the
raw patch bytes and normalizes the scalar model value by sign extension.
Checking an unused signed binding does not admit legacy signed expressions or
getters. Enum and function-type immutable bindings remain unsupported. Other
existing expression/ABI restrictions still apply. The old implicit
substitution of constructor-set addresses with `address(this)` has been removed.
Absent deployment evidence, used immutables fail closed, even when an initializer
appears locally evaluable. Unused immutable declarations need no inferred value.

The model specializes immutable reads to literals. A delegatecall changes the
execution account used by `address(this)` and storage; it does not change these
code-bound literals. Generated code is specialized to the same binding, so its
constructor does not recreate or rebind the original deployment. The report records
the deployment identity and typed bindings; the import digest includes the complete
evidence and checker source, preventing different deployments from sharing that
identity. Re-elaborate the import when deployment evidence changes.

This is a consistency check of submitted evidence, not an authenticated chain query,
constructor proof, or proof of Solidity/bytecode correspondence. Consumers must tie
`codeAddress` and runtime to their intended chain, block and code-loading call frame.
The execution account may differ under delegatecall. Source-gas evidence must refer
to the same original runtime; generated-code gas equivalence remains unclaimed.

Generic differential checks execute real constructors, capture their runtime, and
compare source bytecode, Denote and generated bytecode through direct calls and a
real delegatecall proxy. They exercise getters, inherited/shadowed declarations,
initializer values, a direct-call guard and a calldata-sensitive static child.
Malformed-evidence checks are rejection tests, not property proofs.

Semantic references: [Solidity 0.7.6 immutables](https://docs.soliditylang.org/en/v0.7.6/contracts.html#constant-and-immutable-state-variables)
and [compiler output](https://docs.soliditylang.org/en/v0.7.6/using-the-compiler.html#output-description).
