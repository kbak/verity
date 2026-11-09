"""Exact fixed-byte and memory-revert comparisons across compiler/context profiles."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import sys

from .engine import ROOT, HarnessError, campaign, parse_evm, run_bounded, write_json


def error_string(message):
    return (bytes.fromhex("08c379a0") + (32).to_bytes(32, "big")
            + len(message).to_bytes(32, "big")
            + message.ljust((len(message) + 31) // 32 * 32, b"\0"))


def expected(x, mode):
    """Byte-oriented specification independent of the importer and Denote."""
    if mode < 32:
        width = mode + 1
        return "ok", x.to_bytes(32, "big")[-width:].ljust(32, b"\0")
    literals = {32: b"ABCDE", 33: b"", 34: bytes.fromhex("ff00010203"),
                35: "é".encode(), 36: b"xy", 37: b"short", 41: b"thirty-two"}
    if mode in literals:
        return "ok", literals[mode].ljust(32, b"\0")
    if mode in (38, 39):
        return "revert", error_string(b"ABCDE" if mode == 38 else bytes.fromhex("ff00010203"))
    if mode == 40:
        return "ok", x.to_bytes(32, "big")[:5].ljust(32, b"\0")
    if mode < 64:
        return "ok", bytes(32)
    if mode >= 224:
        width = mode - 223
        return "ok", x.to_bytes(32, "big")[:width].rjust(32, b"\0")
    if mode > 192:
        return "revert", error_string(b"size")
    memory = x.to_bytes(32, "big") + bytes([255]) * 32 + bytes(160)
    offset, size = x & 31, mode - 64
    return "revert", memory[offset:offset + size]


def check_campaign(profile, output, count):
    directory = output / profile
    result = campaign(ROOT / "Contracts/SolidityImportSmoke" /
                      f"differential-fixed-bytes-{profile}.json", directory, count, 7605)
    if result["divergences"]:
        raise HarnessError(f"{profile}: {len(result['divergences'])} execution divergences")
    cases = json.loads((directory / "model-cases.json").read_text())
    routes = [parse_evm(directory / "out/source.txt", cases),
              json.loads((directory / "model-results.json").read_text()),
              parse_evm(directory / "out/compiled.txt", cases)]
    for case, *observations in zip(cases, *routes):
        if profile == "modern-signed":
            status, payload = "ok", int(case["args"][0]).to_bytes(32, "big")
        elif profile == "modern-errors":
            x, mode = map(int, case["args"])
            # Ethereum Keccak selectors, independent of importer/model encoding.
            selector = "de8ee6e0" if mode == 0 else "6198cd26"
            status, payload = "revert", bytes.fromhex(selector) + x.to_bytes(32, "big")
            if mode > 1:
                status, payload = "ok", x.to_bytes(32, "big")
        else:
            status, payload = expected(*map(int, case["args"]))
        for observation in observations:
            actual = bytes.fromhex(observation["data"].removeprefix("0x"))
            if (observation["status"], actual) != (status, payload):
                raise HarnessError(f"{profile}/{case['id']}: independent byte expectation differs")
    print(profile, result["cases"], "cases; exact byte expectations passed", flush=True)
    return {"profile": profile, **result, "independent_payload_checks": "passed"}


REJECTIONS = {
    "dirtyPadding": "memory-revert assembly requires literal-bound narrow scalars",
    "dirtyInteger": "memory-revert assembly requires literal-bound narrow scalars",
    "rootBytes": "narrow fixed-bytes root ABI is outside this slice",
    "indexByte": "fixed-bytes indexing may execute INVALID",
    "nonterminal": "assembly requires a terminal memory revert",
    "unsupportedBuiltin": "memory-revert assembly builtin is unsupported",
    "conditionalAssembly": "memory-revert assembly must be straight-line",
    "dynamicBuffer": "bytes locals require an existing memory buffer",
    "division": "legacy exceptional halt is not modeled",
    "arbitraryLoad": "unsupported Yul builtin mload",
}


def check_rejections(output):
    directory = output / "rejections"
    directory.mkdir()
    reports = []
    for name, reason in REJECTIONS.items():
        driver = directory / f"{name}.lean"
        ty = "bytes5" if name == "rootBytes" else "uint256"
        driver.write_text('import Compiler.SolidityImport.Import\n'
            'solidity_import rejected from "Contracts/SolidityImportSmoke" '
            'entry "FixedBytesMemoryRevertRejections.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "ipfs" }\n'
            '  contract FixedBytesMemoryRevertRejections\n'
            f'  function {name}({ty})\n')
        proc = run_bounded(["lake", "env", "lean", driver], cwd=ROOT, timeout=180)
        log = proc.stdout + proc.stderr
        driver.with_suffix(".log").write_text(log)
        if proc.returncode == 0 or "[solidity-import:unsupported]" not in log or reason not in log:
            raise HarnessError(f"{name}: missing source-located rejection: {log}")
        reports.append({"root": name, "diagnostic": reason})
    write_json(directory / "results.json", reports)
    return reports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    profiles = [f"{release}-{context}" for release in ("legacy", "modern")
                for context in ("zero", "one", "two")] + ["modern-signed", "modern-errors"]
    parser.add_argument("--profile", choices=profiles, action="append")
    parser.add_argument("--cases", type=int, default=32)
    parser.add_argument("--jobs", type=int, default=2)
    args = parser.parse_args()
    if args.cases < 0 or args.jobs < 1:
        parser.error("cases must be nonnegative and jobs positive")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    try:
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            reports = list(pool.map(lambda p: check_campaign(p, output, args.cases),
                                    args.profile or profiles))
        rejections = check_rejections(output)
        write_json(output / "results.json", {"campaigns": reports, "rejections": rejections})
    except (HarnessError, ValueError, OSError) as error:
        print(f"HARNESS ERROR: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
