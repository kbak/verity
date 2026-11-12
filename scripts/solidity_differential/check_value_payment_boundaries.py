"""Admission and rejection boundaries for value calls and selector-word encoding."""
import argparse
import json
from pathlib import Path
from .engine import HarnessError, command, write_json

NATIVE = 'function run(address payable a,uint256 n) external returns(bool) { (bool ok,)=a.call{value:n}(""); return ok; }'
SIGNATURE = 'run(«address payable»,uint256)'
CASES = {
    'native': (NATIVE, SIGNATURE, None),
    'payload': (NATIVE.replace('("")', '("x")'), SIGNATURE, 'empty literal calldata'),
    'gas-option': (NATIVE.replace('value:n', 'value:n,gas:100000'), SIGNATURE, 'only a value option'),
    'increment': (NATIVE.replace('value:n', 'value:n++'), SIGNATURE, 'effect-free scalar'),
    'retained-bytes': (NATIVE.replace('(bool ok,)', '(bool ok,bytes memory data)'), SIGNATURE,
                       'bytes locals require an existing memory buffer'),
    'selector-width': ('function run() external pure returns(uint256) { bytes memory b = '
        'abi.encodeWithSelector(0x12345678,uint256(9)); return b.length; }', 'run()', None),
    'dynamic-selector': ('function run(uint256 s) external pure returns(uint256) { bytes memory b = '
        'abi.encodeWithSelector(bytes4(uint32(s)),uint256(9)); return b.length; }', 'run(uint256)', 'literal four-byte selector'),
    'dynamic-payload': ('function run(bytes memory v) external pure returns(uint256) { bytes memory b = '
        'abi.encodeWithSelector(0x12345678,v); return b.length; }', 'run(bytes)', 'static ABI encoding requires'),
    'abi-v2': ('pragma experimental ABIEncoderV2; contract P { function run() external pure returns(uint256) '
        '{ bytes memory b=abi.encodeWithSelector(0x12345678,uint256(9)); return b.length; } }',
        'run()', 'ABI coder v1'),
    'unbounded-bool': ('function run() external pure returns(bool ok) { assembly { let x := 1 '
        'x := 2 switch 0 case 0 { ok := x } default { ok := 0 } } }', 'run()', 'bounded value'),
    'unguarded-scratch': ('function run(address a) external returns(uint256 n) { assembly { '
        'let ok := call(100000,a,0,0,0,0,32) n := mload(0) } }',
        'run(address)', 'unsupported Yul builtin mload'),
    'short-scratch': ('function run(address a) external returns(uint256 n) { assembly { '
        'let ok := call(100000,a,0,0,0,0,32) switch returndatasize() '
        'case 1 { n := mload(0) } default { n := 0 } } }',
        'run(address)', 'unsupported Yul builtin mload'),
    'scratch-before-call': ('function run() external pure returns(uint256 n) { assembly { n := mload(0) } }',
        'run()', 'unsupported Yul builtin mload'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    results = []
    for name, (body, signature, reason) in CASES.items():
        source = 'pragma solidity 0.7.6; ' + (body if name == 'abi-v2' else 'contract P { ' + body + ' }')
        (out / (name + '.sol')).write_text(source)
        driver = out / (name + '.lean')
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import model from {json.dumps(str(out))} entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none", sourceGas := true }\n'
            f'  contract P\n  function {signature}\n')
        try:
            command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
                    log=out / (name + '.log'), timeout=210)
        except HarnessError:
            log = (out / (name + '.log')).read_text()
            if reason is None or '[solidity-import:unsupported]' not in log or reason not in log:
                raise HarnessError('wrong import rejection: ' + name + '\n' + log)
        else:
            if reason is not None:
                raise HarnessError('unsupported construct admitted: ' + name)
        results.append({'case': name, 'diagnostic': reason})
    write_json(out / 'complete.json', {'cases': results})
    print(f'{len(results)} payment import boundaries passed')


if __name__ == '__main__':
    main()
