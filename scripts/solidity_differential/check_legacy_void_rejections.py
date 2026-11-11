"""Located admission/rejection controls adjacent to legacy void callbacks."""
import argparse
from pathlib import Path
from .engine import HarnessError, command, run_bounded, write_json

INTERFACE = 'interface I { function hook(uint256 n) external; } '
HEADER = 'uint256 stored; '
FUNCTION = 'function run(address target,uint256 n) public { '
CALL = 'I(target).hook(n); '
CASES = {
    'calldata-to-external-memory': ('interface I { function hook(bytes memory b) external; }',
        'function run(address target,bytes calldata b) external { I(target).hook(b); }',
        'run(address,bytes)', None),
    'internal-calldata-copy': ('',
        'function h(bytes memory b) internal pure returns(uint256) { return b.length; } '
        'function run(bytes calldata b) external pure returns(uint256) { return h(b); }',
        'run(bytes)', 'calldata call arguments are outside'),
    'scalar-call': (INTERFACE, FUNCTION + CALL + '}', 'run(address,uint256)', None),
    'post-write': (INTERFACE, FUNCTION + CALL + 'stored=n; }', 'run(address,uint256)',
                   'storage-free trailing continuation'),
    'post-read': (INTERFACE, FUNCTION + CALL + 'require(stored==n); }', 'run(address,uint256)',
                  'storage-free trailing continuation'),
    'post-call-storage-argument': (INTERFACE, FUNCTION + CALL + 'I(target).hook(stored); }',
                                  'run(address,uint256)', 'storage-free trailing continuation'),
    'post-conditional-write': (INTERFACE, FUNCTION + CALL + 'if(n>0) stored=n; }',
                               'run(address,uint256)', 'storage-free trailing continuation'),
    'effectful-argument': (INTERFACE, FUNCTION + 'I(target).hook(n++); }', 'run(address,uint256)',
                           'effect-free'),
    'return-value': (INTERFACE.replace('external;', 'external returns(uint256);'),
                     FUNCTION + CALL + '}', 'run(address,uint256)', 'external calls require'),
    'payable-callee': (INTERFACE.replace('external;', 'external payable;'),
                       FUNCTION + CALL + '}', 'run(address,uint256)', 'external calls require'),
    'abi-v2': ('pragma experimental ABIEncoderV2; ' + INTERFACE, FUNCTION + CALL + '}',
                'run(address,uint256)', 'require ABI coder v1'),
    'dynamic-slot': ('', 'function run(uint256 slot) public view returns(uint256 v) '
                     '{ assembly { v := sload(slot) } }', 'run(uint256)', 'require a constant slot'),
    'constant-word': ('', 'function run() public view returns(uint256 v) '
                     '{ assembly { v := sload(7) } }', 'run()', None),
    'constant-address': ('', 'function run() public view returns(address v) '
                     '{ assembly { v := sload(7) } }', 'run()', None),
    'narrow-slot': ('', 'function run() public view returns(uint8 v) '
                     '{ assembly { v := sload(7) } }', 'run()', 'requires a bounded value'),
    'dirty-assembly-reread': ('', 'function run() public view returns(uint256 v) '
                     '{ address a; assembly { a := sload(7) } assembly { v := a } }',
                     'run()', 'assembly reads require full-word or literal scalars'),
    'storage-write': ('', 'function run() public { assembly { sstore(7,1) } }',
                     'run()', 'requires a terminal memory revert or read-only decoding'),
}


def run(output, prepared=False):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import', '--project-dir', '.'],
                timeout=1800, log=output / 'build.log')
    reports, failures = [], []
    for name, (interface, body, signature, reason) in CASES.items():
        (output / f'{name}.sol').write_text('pragma solidity 0.7.6; ' + interface + 'contract P { ' + HEADER + body + ' }')
        driver = output / f'{name}.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import checked from "{output}" entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            '  contract P\n  function ' + signature + '\n')
        proc = run_bounded(['lake', 'env', 'lean', driver], timeout=180)
        log = proc.stdout + proc.stderr
        driver.with_suffix('.log').write_text(log)
        if reason is None:
            if proc.returncode != 0:
                failures.append(f'{name}: supported root did not import: {log}')
        elif proc.returncode == 0 or '[solidity-import:unsupported]' not in log or reason not in log:
            failures.append(f'{name}: missing located rejection: {log}')
        reports.append({'case': name, 'status': 'admitted' if reason is None else 'rejected', 'diagnostic': reason})
    write_json(output / 'results.json', {'passed': not failures, 'controls': reports, 'failures': failures})
    if failures:
        raise HarnessError('\n'.join(failures))
    print(f'{len(reports)} callback admission/rejection controls passed', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()))
