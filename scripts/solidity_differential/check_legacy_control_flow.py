"""Legacy loops/division: source, model and generated code versus integer/byte oracles.

All terminating test loops are small or bounded by an unsigned word's bit width.
This is finite execution evidence, not a proof of loop or compiler correctness.
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
FUNCTIONS = ("arithmetic", "counted", "shrinking", "decodeLoop")


def ok(*values):
    return "ok", encode(["uint256"] * len(values), [value % MOD for value in values])


def revert(message=None):
    return "revert", b"" if message is None else keccak(b"Error(string)")[:4] + encode(["string"], [message])


def expectation(function, values):
    if function == "modernDivision":
        a, b, mode = values
        if b == 0:
            return "revert", keccak(b"Panic(uint256)")[:4] + encode(["uint256"], [0x12])
        return ok(a // b if mode in (0, 2) else a % b)
    if function in ("arithmetic", "multiply"):
        a, b = values[:2]
        mode = values[2] if function == "arithmetic" else 0
        if mode == 0:
            return ok(a * b) if a * b < MOD else revert()
        if mode in (1, 8):
            return ok(a // b) if b else revert("zero")
        if mode in (2, 3):
            return ok((a % b if mode == 2 else a // b) if b else 0)
        if mode in (4, 5):
            return ok(a // b if mode == 4 else a % b) if b else revert()
        if mode == 6:
            return ok(int(b == 0 or a // b == 1))
        if mode == 7:
            return ok(int(b != 0 and a % b == 0))
        if mode == 9:
            return ok(a // 65 + a % 65)
        if mode == 10:
            return (revert() if a == 0 else ok(0)) if b == 0 else ok(a // b)
        return ok(0)
    if function == "counted":
        n, seed, mode = values
        if n > 12:
            return revert("bound")
        if mode == 5:
            return ok(n * (n // seed), n) if seed else revert("zero")
        iterations = min(n, 3) if mode == 4 else n
        total = iterations * seed + iterations * (iterations - 1) // 2
        if mode == 2:
            total += n
        if mode == 3:
            total = 2 * total + n
        return ok(total, iterations)
    if function == "shrinking":
        a, seed, mode = values
        # Independent arithmetic/bit-position formulas, not a simulated lowered loop.
        if mode == 0:
            return ok(seed + sum(a // (1 << i) for i in range(a.bit_length())), a.bit_length())
        if mode == 1:
            positions = [i for i in range(256) if a & (1 << i)]
            return ok(seed + sum((rank + 1) * (1 << i) for rank, i in enumerate(positions)), len(positions))
        small = a % 256
        count = (small.bit_length() + 1) // 2
        return ok(seed + sum(small // (4 ** i) for i in range(count)), count)
    data, n = values
    if n > 8:
        return revert("bound")
    if len(data) < n * 65:
        return revert("short")
    total = sum(int.from_bytes(data[i * 65:i * 65 + 32], "big") +
                int.from_bytes(data[i * 65 + 32:i * 65 + 64], "big") + data[i * 65 + 64]
                for i in range(n))
    return ok(total, n)


def inputs(function, count):
    rng = random.Random(7607)
    edges = [0, 1, 2, 3, 64, 65, 66, 255, 256, 2**128 - 1, 2**128, 2**255, MOD - 2, MOD - 1]
    if function == "modernDivision":
        return [(a, b, mode) for a in edges for b in [0, 1, 2, 65, MOD - 1] for mode in range(4)]
    if function in ("arithmetic", "multiply"):
        pairs = [(a, b) for a in edges for b in [0, 1, 2, 65, 2**128, MOD - 1]]
        pairs += [(rng.randrange(MOD), rng.choice([0, 1, rng.randrange(MOD)])) for _ in range(count)]
        return [(a, b) if function == "multiply" else (a, b, mode)
                for a, b in pairs for mode in ([0] if function == "multiply" else range(11))]
    if function == "counted":
        rows = [(n, seed, mode) for n in [0, 1, 2, 3, 4, 8, 12, 13, MOD - 1]
                for seed in [0, 1, 2, MOD - 1] for mode in range(6)]
        return rows + [(rng.randrange(14), rng.randrange(MOD), rng.randrange(6)) for _ in range(count)]
    if function == "shrinking":
        return [(a, seed, mode) for a in edges for seed in [0, MOD - 1] for mode in range(3)] + [
            (rng.randrange(MOD), rng.randrange(MOD), rng.randrange(3)) for _ in range(count)]
    rows = [(bytes((17 + 53 * i) % 256 for i in range(length)), n)
            for length in [0, 1, 64, 65, 66, 129, 130, 195, 519, 520, 521]
            for n in [0, 1, 2, 3, 8, 9, MOD - 1]]
    return rows + [(rng.randbytes(rng.randrange(522)), rng.randrange(10)) for _ in range(count)]


def check_campaign(function, context, output, count, optimized=False, config=None):
    directory = output / f"{function}-{context}"
    directory.mkdir()
    if config is None:
        original = ROOT / "Contracts/SolidityImportSmoke" / f"differential-legacy-flow-{function}.json"
        contents = json.loads(original.read_text())
        contents["project"] = str(original.parent)
        contents["contract"] += {"zero": "", "one": "One", "two": "Two"}[context]
        contents["entry"] = contents["contract"] + ".sol"
        contents["settings"]["optimizer"]["enabled"] = optimized
        config = directory / "config.json"
        write_json(config, contents)
    _, metadata, abi, _, _ = prepare(config, directory)
    if context in ("zero", "one", "two"):
        source = json.loads((directory / "source.output.json").read_text())
        layouts = [contract["storageLayout"]["storage"]
                   for contracts in source["contracts"].values() for contract in contracts.values()]
        if max(map(len, layouts), default=0) != {"zero": 0, "one": 1, "two": 2}[context]:
            raise HarnessError("fixture input includes unexpected state declarations")
    if metadata["params"] != [item["name"] for item in abi["inputs"]]:
        raise HarnessError("source/model parameter identities differ")
    types = [item["type"] for item in abi["inputs"]]
    selector = keccak((function + "(" + ",".join(types) + ")").encode())[:4]
    cases, expected = [], []
    for index, values in enumerate(inputs(function, count)):
        raw = encode(types, values)
        expected.append(expectation(function, values))
        cases.append({"id": f"{function}-{index}",
                      "args": [str(int.from_bytes(raw[i:i+32], "big")) for i in range(0, len(raw), 32)],
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
    return {"function": function, "context": context, **result}


REJECTIONS = {
    **{name: "legacy exceptional halt is not modeled" for name in (
        "unguarded", "lateGuard", "stale", "staleAssembly", "wrongBranch", "partialGuard",
        "weakGuard", "truncation", "shortCircuit", "callerGuard", "loopStale", "loopGuard")},
    "inclusive": "counter < invariant bound",
    "narrowCounter": "a for loop counter must be uint256",
    "bodyCounter": "must not be assigned in the loop body",
    "changingBound": "for loop bound must remain invariant",
    "continuing": "does not support Continue",
    "unbounded": "not a recognized bounded bit-clearing or right-shift step",
    "arbitraryWhile": "loops require a supported monotone bound",
    "changedBuffer": "for loop bound must remain invariant",
}


def check_rejections(output):
    directory = output / "rejections"
    directory.mkdir()
    results = []
    for name, reason in REJECTIONS.items():
        for context in ("", "Two"):
            driver = directory / f"{name}{context}.lean"
            params = "bytes, bytes" if name == "changedBuffer" else "uint256, uint256"
            driver.write_text('import Compiler.SolidityImport.Import\n'
                'solidity_import rejected from "Contracts/SolidityImportSmoke" '
                f'entry "LegacyControlFlowRejections{context}.sol"\n'
                '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
                'viaIR := false, optimizerRuns := none, bytecodeHash := "ipfs" }\n'
                f'  contract LegacyControlFlowRejections{context}\n  function {name}({params})\n')
            proc = run_bounded(["lake", "env", "lean", driver], cwd=ROOT, timeout=180)
            log = proc.stdout + proc.stderr
            driver.with_suffix(".log").write_text(log)
            if proc.returncode == 0 or "[solidity-import:unsupported]" not in log or reason not in log:
                raise HarnessError(f"{name}{context}: missing source-located rejection: {log}")
            results.append({"root": name + context, "diagnostic": reason})
    write_json(directory / "results.json", results)
    return results



def check_guard_probe(output):
    """A stale guard must reject; successful import violates that boundary.

    This is an admission mutation, not an exceptional-halt execution test.
    Infrastructure/build failures never count as detecting the mutation.
    """
    directory = output / "guard-probe"
    directory.mkdir()
    fixture = ROOT / "Contracts/SolidityImportSmoke"
    config = json.loads((fixture / "differential-legacy-flow-arithmetic.json").read_text())
    config.update(project=str(fixture), entry="LegacyControlFlowRejections.sol",
                  contract="LegacyControlFlowRejections", function="stale",
                  param_types=["uint256", "uint256"], variables={"a": 256, "b": 256},
                  arguments={"a": "a", "b": "b"})
    config_path = directory / "config.json"
    write_json(config_path, config)
    try:
        prepare(config_path, directory)
    except HarnessError:
        log = (directory / "import.log").read_text() if (directory / "import.log").exists() else ""
        if "[solidity-import:unsupported]" not in log or "legacy exceptional halt is not modeled" not in log:
            raise
        result = {"cases": 0, "divergences": [], "rejections": [{"root": "stale", "status": "rejected"}]}
        write_json(directory / "results.json", result)
        return result
    result = {"cases": 0, "rejections": [], "divergences": [{
        "kind": "admission", "case": {"id": "stale-guard-zero-divisor", "args": ["7", "1"]},
        "expected": "source-rejected", "actual": "successfully imported and compiled",
        "reason": "require(b != 0); b--; return a / b permits a zero divisor at b = 1",
    }]}
    write_json(directory / "results.json", result)
    return result



def check_modern(output):
    directory = output / "modern-source"
    directory.mkdir()
    (directory / "Division.sol").write_text("""// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;
contract Division {
    function modernDivision(uint256 a, uint256 b, uint256 mode) public pure returns (uint256) {
        if (mode == 0) return a / b;
        if (mode == 1) return a % b;
        if (mode == 2) { a /= b; return a; }
        a %= b; return a;
    }
}
""")
    config = {"project": str(directory), "entry": "Division.sol", "contract": "Division",
              "function": "modernDivision", "solc": "0.8.34+commit.80d5c536",
              "param_types": ["uint256"] * 3, "variables": {"a": 256, "b": 256, "mode": 256},
              "arguments": {name: name for name in ("a", "b", "mode")}, "storage": []}
    config_path = directory / "config.json"
    write_json(config_path, config)
    return check_campaign("modernDivision", "modern", output, 0, config=config_path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--cases", type=int, default=16)
    parser.add_argument("--context", choices=["zero", "one", "two"], action="append")
    parser.add_argument("--function", choices=FUNCTIONS, action="append")
    parser.add_argument("--optimized", action="store_true")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--rejections", action="store_true")
    parser.add_argument("--guard-probe", action="store_true")
    parser.add_argument("--modern", action="store_true")
    args = parser.parse_args()
    if args.cases < 0 or args.jobs < 1:
        parser.error("cases must be nonnegative; jobs must be positive")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    pairs = [(fn, context) for fn in (args.function or FUNCTIONS)
             for context in (args.context or ["zero", "one", "two"])]
    try:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results = list(pool.map(lambda pair: check_campaign(*pair, output, args.cases, args.optimized), pairs))
        if args.modern:
            results.append(check_modern(output))
        probe = check_guard_probe(output) if args.guard_probe else {"cases": 0, "divergences": [], "rejections": []}
        results.append({"function": "guard-probe", **probe})
        rejections = (check_rejections(output) if args.rejections else []) + probe["rejections"]
        summary = {"campaigns": results, "cases": sum(r["cases"] for r in results),
                   "divergences": [d for r in results for d in r["divergences"]], "rejections": rejections}
        write_json(output / "results.json", summary)
    except (HarnessError, ValueError, OSError) as error:
        print(f"HARNESS ERROR: {error}", file=sys.stderr)
        return 2
    return int(bool(summary["divergences"]))


if __name__ == "__main__":
    raise SystemExit(main())
