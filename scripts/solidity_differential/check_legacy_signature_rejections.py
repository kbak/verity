"""Fail-closed near misses for the legacy signature-call boundary."""
import argparse
from pathlib import Path
import sys

from .engine import HarnessError, command, run_bounded, write_json

HEADER = '// SPDX-License-Identifier: MIT\npragma solidity 0.7.6;\n'
INTERFACE = ('interface I { function validate(bytes32, bytes memory) '
             'external view returns (bytes4); }\n')
CASES = {
    'concrete-contract': (HEADER +
        'contract Concrete { function validate(bytes32, bytes memory) external view returns(bytes4) '
        '{ return 0x12345678; }} contract P { function run(address a, bytes32 h, bytes memory s) '
        'public view returns(uint256) { return uint256(bytes32(Concrete(a).validate(h,s))); }}',
        'run(address,bytes32,bytes)', 'external contract calls are outside this slice'),
    'wrong-result': (HEADER + INTERFACE.replace('returns (bytes4)', 'returns (uint256)') +
        'contract P { function run(address a, bytes32 h, bytes memory s) public view returns(uint256) '
        '{ return I(a).validate(h,s); }}', 'run(address,bytes32,bytes)',
        'external calls require the ABI-v1 bytes4 view slice'),
    'wrong-hash-type': (HEADER + INTERFACE.replace('validate(bytes32', 'validate(uint256') +
        'contract P { function run(address a, uint256 h, bytes memory s) public view returns(uint256) '
        '{ return uint256(bytes32(I(a).validate(h,s))); }}', 'run(address,uint256,bytes)',
        'external calls require the ABI-v1 bytes4 view slice'),
    'non-view': (HEADER + INTERFACE.replace('external view', 'external') +
        'contract P { function run(address a, bytes32 h, bytes memory s) public returns(uint256) '
        '{ return uint256(bytes32(I(a).validate(h,s))); }}', 'run(address,bytes32,bytes)',
        'external calls require the ABI-v1 bytes4 view slice'),
    'byte-allocation': (HEADER + INTERFACE +
        'contract P { function run(address a, bytes32 h) public view returns(uint256) '
        '{ bytes memory s = new bytes(4); return uint256(bytes32(I(a).validate(h,s))); }}',
        'run(address,bytes32)', 'bytes locals require an existing memory buffer'),
    'memory-write': (HEADER + INTERFACE +
        'contract P { function run(address a, bytes32 h, bytes memory s) public view returns(uint256) '
        '{ bytes memory p; assembly { p := add(s, 32) mstore(p, 4) } '
        'return uint256(bytes32(I(a).validate(h,p))); }}', 'run(address,bytes32,bytes)',
        'is not a writable scalar local'),
    'assertion': (HEADER + 'contract P { function run(bytes32 h) public pure returns(address) '
        '{ assert(h != 0); return ecrecover(h,27,h,h); }}', 'run(bytes32)',
        'builtin call is outside the scalar slice'),
    'abi-v2-root': (HEADER + 'pragma experimental ABIEncoderV2;\n' + INTERFACE +
        'contract P { function run(address a, bytes32 h, bytes memory s) public view returns(uint256) '
        '{ return uint256(bytes32(I(a).validate(h,s))); }}', 'run(address,bytes32,bytes)',
        'require ABI coder v1 at the call site'),
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
    # Coder selection follows the helper's defining source for its call site.
    base = HEADER + 'pragma experimental ABIEncoderV2;\n' + INTERFACE + (
        'contract Base { function helper(address a, bytes32 h, bytes memory s) '
        'internal view returns(uint256) { return uint256(bytes32(I(a).validate(h,s))); }}')
    (output / 'Base.sol').write_text(base)
    cases['abi-v2-helper'] = (HEADER + 'import "./Base.sol";\n' +
        'contract P is Base { function run(address a, bytes32 h, bytes memory s) '
        'public view returns(uint256) { return helper(a,h,s); }}',
        'run(address,bytes32,bytes)', 'require ABI coder v1 at the call site')
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
