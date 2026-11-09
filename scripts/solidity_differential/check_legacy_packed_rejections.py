"""Fail-closed boundaries of legacy static packed hashing."""
import argparse
from pathlib import Path
import sys
from .engine import HarnessError, command, run_bounded, write_json

HEADER = 'pragma solidity 0.7.6;\n'
CASES = {
    'dynamic': (HEADER + 'contract P { function run(bytes memory b) public pure returns(bytes32) '
        '{ return keccak256(abi.encodePacked(b)); }}', 'run(bytes)',
        'requires literal or fixed-width arguments'),
    'direct-buffer': (HEADER + 'contract P { function run(bytes memory b) public pure returns(bytes32) '
        '{ return keccak256(b); }}', 'run(bytes)', 'legacy hashing requires abi.encodePacked'),
    'standard-encoding': (HEADER + 'contract P { function run(bytes32 b) public pure returns(bytes32) '
        '{ return keccak256(abi.encode(b)); }}', 'run(bytes32)',
        'byte construction is outside the decoding slice'),
    'nested-hash': (HEADER + 'contract P { function run(bytes32 b) public pure returns(bytes32) '
        '{ return keccak256(abi.encodePacked(keccak256(abi.encodePacked(b)))); }}', 'run(bytes32)',
        'require scalar values or conversions'),
    'helper-argument': (HEADER + 'contract P { function h(bytes32 b) internal pure returns(bytes32) '
        '{ return b; } function run(bytes32 b) public pure returns(bytes32) '
        '{ return keccak256(abi.encodePacked(h(b))); }}', 'run(bytes32)',
        'require scalar values or conversions'),
    'assignment': (HEADER + 'contract P { function run(uint256 b) public pure returns(bytes32) '
        '{ return keccak256(abi.encodePacked(b++)); }}', 'run(uint256)',
        'require scalar values or conversions'),
    'constructed-helper-argument': (HEADER + 'contract P { '
        'function h(bytes memory b) internal pure returns(uint256) { return b.length; } '
        'function run(bytes32 b) public pure returns(uint256) '
        '{ return h(abi.encodePacked(b)); }}', 'run(bytes32)',
        'byte construction is outside the decoding slice'),
    'allocated-local': (HEADER + 'contract P { function run(bytes32 b) public pure returns(bytes32) '
        '{ bytes memory c = abi.encodePacked(b); return keccak256(c); }}', 'run(bytes32)',
        'bytes locals require an existing memory buffer'),
    'allocated-return': (HEADER + 'contract P { function run(bytes32 b) public pure returns(bytes memory) '
        '{ return abi.encodePacked(b); }}', 'run(bytes32)', 'dynamic bytes returns'),
    'abi-v2-root': (HEADER + 'pragma experimental ABIEncoderV2; contract P { '
        'function run(bytes32 b) public pure returns(bytes32) '
        '{ return keccak256(abi.encodePacked(b)); }}', 'run(bytes32)',
        'requires ABI coder v1 at the call site'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import', '--project-dir', '.'],
            timeout=1800, log=output / 'build.log')
    cases = dict(CASES)
    (output / 'Base.sol').write_text(HEADER + 'pragma experimental ABIEncoderV2;\n' +
        'contract Base { function helper(bytes32 h) internal pure returns(bytes32) '
        '{ return keccak256(abi.encodePacked(h)); }}')
    cases['abi-v2-helper'] = (HEADER + 'import "./Base.sol";\n' +
        'contract P is Base { function run(bytes32 h) public pure returns(bytes32) '
        '{ return helper(h); }}', 'run(bytes32)', 'requires ABI coder v1 at the call site')
    reports = []
    for name, (source, signature, reason) in cases.items():
        (output / f'{name}.sol').write_text(source)
        driver = output / f'{name}.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            'open Compiler.CompilationModel.SolidityImport\n'
            f'solidity_import rejected from "{output}" entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            f'  contract P\n  function {signature}\n')
        result = run_bounded(['lake', 'env', 'lean', driver], timeout=180)
        log = result.stdout + result.stderr
        driver.with_suffix('.log').write_text(log)
        if result.returncode == 0 or '[solidity-import:unsupported]' not in log or reason not in log:
            raise HarnessError(f'{name}: missing located rejection: {log}')
        reports.append({'case': name, 'diagnostic': reason})
    write_json(output / 'results.json', {'passed': True, 'rejections': reports})
    return 0


if __name__ == '__main__':
    sys.exit(main())
