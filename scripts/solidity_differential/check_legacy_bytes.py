"""Legacy bytes ABI and physical-memory reads against solc and a byte-level oracle.

Cases have complete calldata words, as required by the existing read-only
adapter. Truncation of tails/heads is still exercised. Gas and huge allocations
are not modeled; every executed memory address is small, including modular
arithmetic cases whose final addresses wrap back into ordinary memory.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import random
import sys

from eth_abi import encode
from .cases import keccak
from .engine import ROOT, HarnessError, execute, parse_evm, prepare, run_bounded, write_json

MOD = 1 << 256


def word(value):
    return value.to_bytes(32, "big")


def expectation(function, payload):
    """Decode v1 calldata, then read explicit bytes; no importer/Yul expressions."""
    arity = 2 if function == "decode" else 3
    if len(payload) < 32 * arity:
        return "revert", b""
    read = lambda offset: int.from_bytes(payload[offset:offset + 32], "big")
    memory = bytearray(8192)
    free = 128
    lengths = []
    for i in range(arity - 1):
        offset = read(32 * i)
        if offset > 2**32 or offset + 32 > len(payload):
            return "revert", b""
        size = read(offset)
        if size > 2**32 or offset + 32 + size > len(payload):
            return "revert", b""
        if free + 64 + size > len(memory):
            raise HarnessError("oracle memory domain exceeded")
        memory[free:free + 32] = word(size)
        memory[free + 32:free + 32 + size] = payload[offset + 32:offset + 32 + size]
        memory[free + 32 + size:free + 64 + size] = bytes(32)
        free += 32 + ((size + 31) // 32) * 32
        memory[64:96] = word(free)
        lengths.append(size)
    index = read(32 * (arity - 1))
    def load(offset):
        offset %= MOD
        if offset + 32 > len(memory):
            raise HarnessError("case requests an unbounded memory read")
        return bytes(memory[offset:offset + 32])
    if function == "decode":
        base = (128 + 32 + 65 * index) % MOD
        first, second, lane = load(base), load(base + 32), load(base + 64)[0]
        return "ok", word(lane) + first + second
    return "ok", load(128 + index) + word(lengths[0]) + word(lengths[1])


def payloads(function, count, seed):
    rng = random.Random(seed)
    def pack(data, index, following=b""):
        if function == "decode":
            return encode(["bytes", "uint256"], [data, index])
        return encode(["bytes", "bytes", "uint256"], [data, following, index])
    rows = []
    for length in [0, 1, 2, 31, 32, 33, 63, 64, 65, 66, 95, 96, 97, 129, 130, 131, 195]:
        data = bytes((17 + i * 53) % 256 for i in range(length))
        indexes = [0, 1, 2, 3, MOD - 1] if function == "decode" else [0, 1, 31, 32, 33, 63, 64, 65, 96, 128]
        for index in indexes:
            rows.append((f"length-{length}-offset-{index}", pack(data, index, bytes(range(70)))))
    for i in range(count):
        length = rng.randrange(257)
        index = rng.randrange(5 if function == "decode" else 320)
        data = rng.randbytes(length)
        rows.append((f"random-{seed}-{i}", pack(data, index, rng.randbytes(rng.randrange(100)))))
    # Pointer arithmetic wraps before mload: inspect scratch/free-pointer/header bytes.
    for address in [0, 1, 31, 32, 63, 64, 65, 95, 96, 127, 128, 129, 160]:
        index = ((address - 160) * pow(65, -1, MOD)) % MOD if function == "decode" else (address - 128) % MOD
        rows.append((f"wrapped-address-{address}", pack(bytes(range(130)), index, b"neighbor")))
    baseline = pack(b"x", 0, b"next")
    for words in range(len(baseline) // 32):
        rows.append((f"truncated-{words}-words", baseline[:words * 32]))
    for offset in [0, 1, 31, 32, 33, 64, 96, len(baseline), 2**32, 2**32 + 1, 2**64, MOD - 1]:
        rows.append((f"abi-offset-{offset}", word(offset) + baseline[32:]))
    header = int.from_bytes(baseline[:32], "big")
    for length in [0, 1, 2, 31, 32, 33, len(baseline), 2**32, 2**32 + 1, MOD - 1]:
        rows.append((f"abi-length-{length}", baseline[:header] + word(length) + baseline[header + 32:]))
    # Poison unused calldata padding; calldatacopy(length) + mstore(end, 0) clears it.
    for length in [0, 1, 31, 32, 33, 64, 65]:
        raw = bytearray(pack(bytes([0xAB]) * length, 1 if function == "decode" else 32, b"next"))
        start = int.from_bytes(raw[:32], "big") + 32 + length
        finish = (start + 31) // 32 * 32
        raw[start:finish] = bytes([0xFF]) * (finish - start)
        rows.append((f"dirty-padding-{length}", bytes(raw)))
    return rows


def check_campaign(function, context, output, count, config=None):
    directory = output / f"{function}-{context}"
    config = config or ROOT / "Contracts/SolidityImportSmoke" / f"differential-legacy-bytes-{function}-{context}.json"
    _, metadata, abi, _, _ = prepare(config, directory)
    if metadata["params"] != [item["name"] for item in abi["inputs"]]:
        raise HarnessError("source/model parameter identities differ")
    signature = function + "(" + ",".join(item["type"] for item in abi["inputs"]) + ")"
    selector = keccak(signature.encode())[:4]
    cases, expected = [], []
    for name, raw in payloads(function, count, 7606):
        if len(raw) % 32:
            raise HarnessError("read-only adapter requires complete calldata words")
        expected.append(expectation(function, raw))
        cases.append({"id": name, "args": [str(int.from_bytes(raw[i:i+32], "big")) for i in range(0, len(raw), 32)],
                      "timestamp": "0", "storage": [], "observe": [], "storageCount": 0, "observeCount": 0,
                      "sourceCalldata": "0x" + (selector + raw).hex(),
                      "compiledCalldata": "0x12345678" + raw.hex()})
    manifest_path = directory / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["casesSha256"] = hashlib.sha256(json.dumps(cases, sort_keys=True).encode()).hexdigest()
    write_json(manifest_path, manifest)
    result = execute(directory, cases)
    routes = [parse_evm(directory / "out/source.txt", cases),
              json.loads((directory / "model-results.json").read_text()),
              parse_evm(directory / "out/compiled.txt", cases)]
    for i, (status, data) in enumerate(expected):
        for route in routes:
            if (route[i]["status"], bytes.fromhex(route[i]["data"].removeprefix("0x"))) != (status, data):
                result["divergences"].append({"case": cases[i], "expectedStatus": status,
                                              "expectedData": "0x" + data.hex(), "actual": route[i]})
    print(function, context, result["cases"], "cases;", len(result["divergences"]), "divergences", flush=True)
    return {"function": function, "context": context, **result,
            "independent_bytes": "failed" if result["divergences"] else "passed"}


# Default bytes references and pointer writes are now positive controls in
# check_legacy_byte_pointers (empty/zero), not unsupported constructs.
REJECTIONS = [
    ("helperDirtyWrite", "bytes", "Yul assignment to narrow local requires a bounded value"),
    ("dirtyWriteTwo", "bytes", "Yul assignment to narrow local requires a bounded value"),
    ("encodedArgument", "uint256", "byte construction is outside the decoding slice"),
    ("replacement", "bytes", "bytes assignment requires an existing memory buffer"),
    ("index", "bytes, uint256", "bytes indexing may execute INVALID"),
    ("allocate", "uint256", "bytes locals require an existing memory buffer"),
    ("returnBytes", "bytes", "dynamic bytes returns are outside the decoding slice"),
    ("calldataBuffer", "bytes", None),  # Retain the newly supported root as a positive control.
    ("dirtyRead", "bytes, uint256", "assembly reads require full-word or literal scalars"),
    ("dirtyWrite", "bytes", "Yul assignment to narrow local"),
    ("memoryWrite", "bytes", "free-pointer root and constant displacement"),
    ("literalBuffer", "uint256", "bytes helpers require an existing memory buffer"),
    ("decode", "bytes, uint256", "bytes memory requires ABI coder v1"),
]


def check_rejections(output):
    directory = output / "rejections"
    directory.mkdir()
    reports = []
    for name, params, reason in REJECTIONS:
        contract = "LegacyByteMemoryV2" if name == "decode" else "LegacyByteMemoryRejections"
        entry = contract
        if name == "dirtyWriteTwo":
            contract = "LegacyByteMemoryRejectionsTwo"
        function = "dirtyWrite" if name == "dirtyWriteTwo" else name
        driver = directory / f"{name}.lean"
        driver.write_text('import Compiler.SolidityImport.Import\n'
            'solidity_import rejected from "Contracts/SolidityImportSmoke" '
            f'entry "{entry}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "ipfs" }\n'
            f'  contract {contract}\n  function {function}({params})\n')
        proc = run_bounded(["lake", "env", "lean", driver], cwd=ROOT, timeout=180)
        log = proc.stdout + proc.stderr
        driver.with_suffix(".log").write_text(log)
        if reason is None:
            if proc.returncode != 0:
                raise HarnessError(f"{name}: required positive import control failed: {log}")
            reports.append({"root": name, "accepted": True})
            continue
        if proc.returncode == 0 or "[solidity-import:unsupported]" not in log or reason not in log:
            raise HarnessError(f"{name}: missing source-located rejection: {log}")
        reports.append({"root": name, "diagnostic": reason})
    write_json(directory / "results.json", reports)
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=32)
    parser.add_argument("--context", choices=["zero", "one", "two"], action="append")
    parser.add_argument("--function", choices=["decode", "inspect"], action="append")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--rejections", action="store_true")
    args = parser.parse_args()
    if args.cases < 0 or args.jobs < 1:
        parser.error("cases must be nonnegative; jobs must be positive")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    pairs = [(fn, context) for fn in (args.function or ["decode", "inspect"])
             for context in (args.context or ["zero", "one", "two"])]
    try:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results = list(pool.map(lambda pair: check_campaign(*pair, output, args.cases), pairs))
        rejections = check_rejections(output) if args.rejections else []
        summary = {"campaigns": results, "cases": sum(r["cases"] for r in results),
                   "divergences": [d for r in results for d in r["divergences"]], "rejections": rejections}
        write_json(output / "results.json", summary)
    except (HarnessError, ValueError, OSError) as error:
        print(f"HARNESS ERROR: {error}", file=sys.stderr)
        return 2
    return int(bool(summary["divergences"]))


if __name__ == "__main__":
    raise SystemExit(main())
