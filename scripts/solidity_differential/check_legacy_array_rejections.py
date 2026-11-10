"""Unsupported array failure paths must produce located import diagnostics."""
import argparse
from pathlib import Path

from .engine import HarnessError, command, run_bounded, write_json

CASES = {
    'unguarded': ('return uint256(items[0]);', 'exact array-length loop guard'),
    'wrong-bound': ('uint256 total; for (uint256 i=0; i<n; ++i) total += uint256(items[i]); return total;',
                    'exact array-length loop guard'),
    'off-by-one': ('for (uint256 i=0; i<items.length; ++i) n += uint256(items[i+1]); return n;',
                   'exact array-length loop guard'),
    'mutable-bound': ('uint256 size=items.length; size+=1; '
                      'for (uint256 i=0; i<size; ++i) n += uint256(items[i]); return n;',
                      'exact array-length loop guard'),
    'counter-write': ('for (uint256 i=0; i<items.length; ++i) { ++i; n += uint256(items[i]); } return n;',
                      'exact array-length loop guard'),
    'element-write': ('for (uint256 i=0; i<items.length; ++i) items[i]=address(2); return n;',
                      'address-array writes'),
    'tuple-write': ('for (uint256 i=0; i<items.length; ++i) (items[i],n)=(address(2),3); return n;',
                    'address-array writes'),
    'array-alias': ('items=new address[](1); return n;', 'address-array writes'),
    'allocation': ('address[] memory other=new address[](n); return other.length;',
                   'does not support NewExpression'),
    'helper': ('return bad(items);', 'exact array-length loop guard'),
}


def run(output, prepared=False):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import', '--project-dir', '.'],
                timeout=1800, log=output / 'build.log')
    cases = {name: ('', 'function run(address[] memory items,uint256 n) public pure returns(uint256) { '
                   + body + ' } function bad(address[] memory a) internal pure returns(uint256) '
                     '{ return uint256(a[0]); }', 'run(address[],uint256)', reason)
             for name, (body, reason) in CASES.items()}
    cases.update({
        'different-array-bound': ('', 'function run(address[] memory items,address[] memory other) public pure '
            'returns(uint256 n) { for(uint256 i=0; i<other.length; ++i) n+=uint256(items[i]); }',
            'run(address[],address[])', 'exact array-length loop guard'),
        'abi-v2': ('pragma experimental ABIEncoderV2;',
            'function run(address[] memory items,uint256) public pure returns(uint256) { return items.length; }',
            'run(address[],uint256)', 'address arrays require ABI coder v1'),
        'calldata': ('', 'function run(address[] calldata items,uint256) external pure returns(uint256) '
            '{ return items.length; }', 'run(address[],uint256)', 'does not support type address[] calldata'),
        'array-return': ('', 'function run(address[] memory items,uint256) public pure returns(address[] memory) '
            '{ return items; }', 'run(address[],uint256)', 'array returns are outside'),
        'other-element': ('', 'function run(uint256[] memory items,uint256) public pure returns(uint256) '
            '{ return items.length; }', 'run(uint256[],uint256)', 'does not support type'),
        'assembly-reference': ('', 'function run(address[] memory items,uint256 n) public pure returns(uint256) '
            '{ assembly { n := mload(items) } return n; }',
            'run(address[],uint256)', 'assembly array references'),
    })
    reports = []
    for name, (pragma, body, signature, reason) in cases.items():
        (output / f'{name}.sol').write_text('pragma solidity 0.7.6; ' + pragma + ' contract P { ' + body + ' }')
        driver = output / f'{name}.lean'
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import rejected from "{output}" entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            '  contract P\n  function ' + signature.replace('address[]', '«address[]»').replace('uint256[]', '«uint256[]»') + '\n')
        proc = run_bounded(['lake', 'env', 'lean', driver], timeout=180)
        log = proc.stdout + proc.stderr
        driver.with_suffix('.log').write_text(log)
        if proc.returncode == 0 or '[solidity-import:unsupported]' not in log or reason not in log:
            raise HarnessError(f'{name}: missing located rejection: {log}')
        reports.append({'case': name, 'diagnostic': reason})
    write_json(output / 'results.json', {'passed': True, 'rejections': reports})
    print(f'{len(reports)} located array rejection controls passed', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()))
