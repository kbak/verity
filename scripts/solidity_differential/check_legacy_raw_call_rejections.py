"""Located rejection controls adjacent to the legacy raw-call slice."""
import argparse
from pathlib import Path

from .engine import HarnessError, command, run_bounded, write_json

HEADER = 'uint256 stored; event Seen(uint256); enum E { A, B } '
SIGNATURE = 'run(address,bytes,uint256)'
FUNCTION = ('function run(address target,bytes memory data,uint256 n) public returns(bool ok) { ')
CALL = 'assembly { ok := call(n,target,0,add(data,32),mload(data),0,0) } '
CASES = {
    'post-write': (FUNCTION + CALL + 'stored=n; }', SIGNATURE, 'storage-free trailing continuation'),
    'post-read': (FUNCTION + CALL + 'return stored>0; }', SIGNATURE, 'storage-free trailing continuation'),
    'post-log': (FUNCTION + CALL + 'emit Seen(n); }', SIGNATURE, None),
    'post-log-storage-read': (FUNCTION + CALL + 'emit Seen(stored); }', SIGNATURE,
                              'storage-free trailing continuation'),
    'post-branch-read': (FUNCTION + CALL + 'if(ok) return stored>0; }', SIGNATURE,
                         'storage-free trailing continuation'),
    'output-area': (FUNCTION + CALL.replace('mload(data),0,0', 'mload(data),0,32') + '}',
                    SIGNATURE, 'empty output area'),
    'nonzero-output-pointer': (FUNCTION + CALL.replace('mload(data),0,0', 'mload(data),32,0') + '}',
                               SIGNATURE, 'empty output area'),
    'nested-call': (FUNCTION + CALL.replace('ok := call(n,target,0,',
                     'ok := call(call(n,target,0,0,0,0,0),target,0,') + '}',
                    SIGNATURE, 'unsupported Yul builtin call'),
    'partial-returndata': (FUNCTION + CALL + 'assembly { let p := mload(64) '
        'returndatacopy(p,0,31) revert(p,31) } }', SIGNATURE, 'assembly builtin is unsupported'),
    'offset-returndata': (FUNCTION + CALL + 'assembly { let p := mload(64) '
        'returndatacopy(p,1,returndatasize()) revert(p,returndatasize()) } }',
         SIGNATURE, 'assembly builtin is unsupported'),
    'live-returndata': (FUNCTION + CALL + 'assembly { let p := mload(64) '
        'returndatacopy(p,0,returndatasize()) } }', SIGNATURE, 'requires a terminal memory revert'),
    'enum-helper-write': ('function h(E e) internal pure returns(bool) { '
        'assembly { e := 1 } return e==E.A; } '
        'function run(E e) public pure returns(bool) { return h(e); }',
        'run(E)', 'assignment to an enum'),
    'public-enum-helper-return': ('function h(E e) public pure returns(E) { return e; } '
        'function run(E e) public pure returns(uint256) { return uint256(h(e)); }',
        'run(E)', 'enum helper returns are outside'),
    'payable-entry': (FUNCTION.replace('public returns', 'public payable returns') + CALL + '}',
                       SIGNATURE, None),
}


def run(output, prepared=False):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import', '--project-dir', '.'],
                timeout=1800, log=output / 'build.log')
    reports = []
    for name, (body, signature, reason) in CASES.items():
        (output / f'{name}.sol').write_text('pragma solidity 0.7.6; contract P { ' + HEADER + body + ' }')
        driver = output / f'{name}.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import rejected from "{output}" entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            '  contract P\n  function ' + signature + '\n')
        proc = run_bounded(['lake', 'env', 'lean', driver], timeout=180)
        log = proc.stdout + proc.stderr
        driver.with_suffix('.log').write_text(log)
        if reason is None:
            if proc.returncode != 0:
                raise HarnessError(f'{name}: supported root did not import: {log}')
        elif proc.returncode == 0 or '[solidity-import:unsupported]' not in log or reason not in log:
            raise HarnessError(f'{name}: missing located rejection: {log}')
        reports.append({'case': name, 'status': 'admitted' if reason is None else 'rejected', 'diagnostic': reason})
    write_json(output / 'results.json', {'passed': True, 'rejections': reports})
    print(f'{len(reports)} raw-call admission/rejection controls passed', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()))
