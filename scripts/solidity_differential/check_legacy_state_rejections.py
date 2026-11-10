"""Reached modifiers and state-changing helpers retain the legacy failure boundary."""
import argparse
from pathlib import Path

from .engine import HarnessError, command, run_bounded, write_json

CASES = {
    'payable': ('function run(uint256 x) public payable { stored = x; }', 'payable functions are outside'),
    'modifier-assert': ('modifier guard(uint256 x) { assert(x != 0); _; } '
        'function run(uint256 x) public guard(x) { stored = x; }', 'assert/INVALID is not modeled'),
    'modifier-division': ('modifier guard(uint256 x) { stored = 12 / x; _; } '
        'function run(uint256 x) public guard(x) { stored = x; }', 'legacy exceptional halt is not modeled'),
    'helper-assert': ('function helper(uint256 x) internal { stored = x; assert(x != 0); } '
        'function run(uint256 x) public { helper(x); }', 'assert/INVALID is not modeled'),
    'helper-division': ('function helper(uint256 x) internal { stored = 12 / x; } '
        'function run(uint256 x) public { helper(x); }', 'legacy exceptional halt is not modeled'),
    'assembly-write': ('function run(uint256 x) public { assembly { sstore(0, x) } }',
        'assembly requires a terminal memory revert or read-only decoding'),
    'external-write': ('function run(uint256 x) public { this.other(x); } '
        'function other(uint256 x) external { stored = x; }', 'external calls require the ABI-v1 bytes4 view slice'),
    'array-write': ('uint256[] private items; function run(uint256 x) public { items.push(x); }',
        'does not support type'),
}


def run(output):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import', '--project-dir', '.'],
            timeout=1800, log=output / 'build.log')
    reports = []
    for name, (body, reason) in CASES.items():
        (output / f'{name}.sol').write_text('pragma solidity 0.7.6; contract P { uint256 stored; ' + body + ' }')
        driver = output / f'{name}.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import rejected from "{output}" entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            '  contract P\n  function run(uint256)\n')
        proc = run_bounded(['lake', 'env', 'lean', driver], timeout=180)
        log = proc.stdout + proc.stderr
        driver.with_suffix('.log').write_text(log)
        if proc.returncode == 0 or '[solidity-import:unsupported]' not in log or reason not in log:
            raise HarnessError(f'{name}: missing located rejection: {log}')
        reports.append({'case': name, 'diagnostic': reason})
    write_json(output / 'results.json', {'passed': True, 'rejections': reports})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    run(parser.parse_args().output)
