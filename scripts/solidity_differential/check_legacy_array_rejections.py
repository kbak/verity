"""Unsupported array failure paths must produce located import diagnostics."""
import argparse
from pathlib import Path

from .engine import HarnessError, command, run_bounded, write_json

# Former guarded-read rejection cases are executable positive/failure cases in
# check_legacy_memory_arrays: they must agree on exact INVALID, not just import.
CASES = {
    'counter-write': ('for (uint256 i=0; i<items.length; ++i) { ++i; n += uint256(items[i]); } return n;',
                      'counter must not be assigned'),
    'tuple-write': ('for (uint256 i=0; i<items.length; ++i) (items[i],n)=(address(2),3); return n;',
                    'tuple address-array writes'),
    'array-alias': ('items=new address[](1); return n;', 'address-array reference writes'),
    'tuple-alias': ('(items,n)=(new address[](1),2); return n;', 'address-array reference writes'),
    'uninitialized': ('address[] memory other; return other.length;', 'require an explicit initializer'),
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
        'abi-v2': ('pragma experimental ABIEncoderV2;',
            'function run(address[] memory items,uint256) public pure returns(uint256) { return items.length; }',
            'run(address[],uint256)', 'address arrays require ABI coder v1'),
        'calldata': ('', 'function run(address[] calldata items,uint256) external pure returns(uint256) '
            '{ return items.length; }', 'run(address[],uint256)', 'does not support type address[] calldata'),
        'abi-v2-return': ('pragma experimental ABIEncoderV2;',
            'function run(uint256 n) public pure returns(address[] memory) '
            '{ address[] memory a = new address[](n); return a; }', 'run(uint256)', 'address arrays require ABI coder v1'),
        'other-element': ('', 'function run(uint256[] memory items,uint256) public pure returns(uint256) '
            '{ return items.length; }', 'run(uint256[],uint256)', 'does not support type'),
        'assembly-reference': ('', 'function run(address[] memory items,uint256 n) public pure returns(uint256) '
            '{ assembly { n := mload(items) } return n; }',
            'run(address[],uint256)', 'assembly array references'),
    })
    traversal = ('mapping(address=>address) links; '
        'function run(uint256 size) public view returns(address[] memory) { '
        'address[] memory items=new address[](size); uint256 i=0; '
        'address cursor=links[address(1)]; while(cursor!=address(1)) { '
        'items[i]=cursor; cursor=links[cursor]; ++i; } return items; }')
    for name, old, new in (
        ('traversal-start', 'uint256 i=0;', 'uint256 i=1;'),
        ('traversal-step', '++i;', 'i+=2;'),
        ('traversal-offset', 'items[i]=cursor;', 'items[i+1]=cursor;'),
        ('traversal-conditional-write', 'items[i]=cursor;',
         'if(i<size) items[i]=cursor;'),
        ('traversal-missing-write', 'items[i]=cursor;', ''),
        ('traversal-hidden-step', 'cursor=links[cursor];', 'cursor=links[address(i++)];'),
    ):
        cases[name] = ('', traversal.replace(old, new), 'run(uint256)',
                       'address traversal requires write, cursor update, and unit index step')
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
