"""Located admission boundaries for legacy calldata and scratch-memory assembly."""
import argparse
from pathlib import Path

from .engine import HarnessError, command, run_bounded, write_json

HEADER = 'pragma solidity 0.7.6;\n'
CASES = {
    'calldata-memory-helper': ('function h(bytes memory b) internal pure returns(uint256) '
        '{ return b.length; } function run(bytes calldata b) public pure returns(uint256) '
        '{ return h(b); }', 'run(bytes)', None),
    'allocator-write': ('function run() public pure { assembly { mstore(64, 0) } }',
        'run()', 'free-pointer root and constant displacement'),
    'existing-buffer-write': ('function run(bytes memory b) public pure { '
        'assembly { mstore(b, 0) } }', 'run(bytes)', 'free-pointer root and constant displacement'),
    'variable-destination': ('function run(uint256 offset) public pure { '
        'assembly { let p := mload(64) mstore(add(p, offset), 0) } }',
        'run(uint256)', 'free-pointer root and constant displacement'),
    'lost-pointer': ('function run() public pure { assembly { '
        'let p := mload(64) p := 0 mstore(p, 1) } }', 'run()',
        'free-pointer root and constant displacement'),
    'negative-displacement': ('function run() public pure { assembly { '
        'let p := mload(64) mstore(sub(p, 32), 1) } }', 'run()',
        'free-pointer root and constant displacement'),
    'wrapping-displacement': ('function run() public pure { assembly { '
        'let p := mload(64) mstore(add(p, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff), 1) } }',
        'run()', 'free-pointer root and constant displacement'),
    'loop': ('function run() public pure { assembly { let p := mload(64) '
        'for { let i := 0 } lt(i, 2) { i := add(i, 1) } { mstore(p, i) } } }',
        'run()', 'requires straight-line assembly'),
    'reassigned-address': ('function run(address a) public pure returns(bytes32 result) { '
        'a = address(uint160(a)+1); assembly { let p := mload(64) mstore(p, a) '
        'result := keccak256(p, 32) } }', 'run(address)', 'require full-word or literal scalars'),
    'local-narrow': ('function run(uint256 x) public pure returns(bytes32 result) { '
        'uint8 a = uint8(x); assembly { let p := mload(64) mstore(p, a) '
        'result := keccak256(p, 32) } }', 'run(uint256)', 'require full-word or literal scalars'),
    'enum-assignment': ('enum E { A, B } function run(E e) public pure returns(uint256) { '
        'assembly { e := 1 } return uint256(e); }', 'run(E)', 'assignment to an enum'),
    'calldata-index': ('function run(bytes calldata b) public pure returns(bytes1) { return b[0]; }',
        'run(bytes)', 'calldata indexing is outside'),
    'calldata-local': ('function run(bytes calldata b) public pure returns(uint256) { '
        'bytes calldata c = b; return c.length; }', 'run(bytes)', 'bytes locals require'),
    'calldata-reassign': ('function run(bytes calldata b, bytes calldata c) public pure returns(uint256) '
        '{ b = c; return b.length; }', 'run(bytes,bytes)', 'calldata assignment is outside'),
    'enum-local': ('enum E { A, B } function run(E e) public pure returns(uint256) { '
        'E c = e; return uint256(c); }', 'run(E)', 'enum locals are outside'),
    # Comparisons and enum helper inputs now have executable positive/INVALID
    # cases in check_legacy_raw_calls. Keep the adjacent unsupported boundary.
    'enum-helper-return': ('enum E { A, B } function h(E e) internal pure returns(E) { '
        'return e; } function run(E e) public pure returns(uint256) { return uint256(h(e)); }',
        'run(E)', 'enum helper returns are outside'),
    'enum-external-argument': ('enum E { A, B } function h(E e) external pure returns(uint256) { '
        'return uint256(e); } function run(E e) public view returns(uint256) { return this.h(e); }',
        'run(E)', 'enum arguments require an internal helper'),
    'enum-named-return': ('enum E { A, B } function run(E e) public pure returns(E r) { '
        'r = e; }', 'run(E)', 'enum returns require one unnamed scalar result'),
    'enum-multiple-returns': ('enum E { A, B } function run(E e) public pure returns(E,uint256) { '
        'return (e,1); }', 'run(E)', 'enum returns require one unnamed scalar result'),
    'enum-key': ('enum E { A, B } mapping(E => uint256) m; '
        'function run(E e) public view returns(uint256) { return m[e]; }',
        'run(E)', 'enum keys require an unsigned conversion'),
    'enum-storage': ('enum E { A, B } E stored; function run() public view returns(uint256) '
        '{ return uint256(stored); }', 'run()', 'enum storage is outside'),
    'v2': ('function run(bytes calldata b) public pure returns(bytes32 result) { '
        'assembly { let p := mload(64) calldatacopy(p, b.offset, b.length) '
        'result := keccak256(p, b.length) } }', 'run(bytes)', 'requires ABI coder v1'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    if not args.prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import'], timeout=1800)
    reports = []
    for name, (body, signature, reason) in CASES.items():
        pragma = 'pragma experimental ABIEncoderV2;\n' if name == 'v2' else ''
        (output/f'{name}.sol').write_text(HEADER+pragma+'contract P { '+body+' }')
        driver = output/f'{name}.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import rejected from "{output}" entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            f'  contract P\n  function {signature}\n')
        result = run_bounded(['turbo-lean', '--json', 'check', str(driver)], timeout=180)
        log = result.stdout+result.stderr
        driver.with_suffix('.log').write_text(log)
        if reason is None:
            if result.returncode != 0:
                raise HarnessError(f'{name}: supported root did not import: {log}')
        elif result.returncode == 0 or '[solidity-import:unsupported]' not in log or reason not in log:
            raise HarnessError(f'{name}: missing located rejection: {log}')
        reports.append(dict(case=name, status='admitted' if reason is None else 'rejected',
                            diagnostic=reason))
    write_json(output/'results.json', dict(passed=True, rejections=reports))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
