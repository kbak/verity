"""Fail-closed import, compilation and unmetered-transport controls for source gas."""
import argparse
import json
from pathlib import Path

from .engine import HarnessError, command, write_json

CASES = {
    'checked-sub-helper': ('function h(uint256 a,uint256 b) internal pure returns(uint256) '
        '{ require(b<=a); return a-b; } function run() external view returns(uint256) '
        '{ uint256 first=gasleft(); return h(first,gasleft()); }', True, None),
    'two-calldata-copies': ('function h(bytes memory a,bytes memory b,uint256 g) '
        'internal pure returns(uint256) { return a.length+b.length+g; } '
        'function run(bytes calldata a,bytes calldata b) external view returns(uint256) '
        '{ return h(a,b,gasleft()); }', True, 'explicit evaluation-order support'),
    'hidden-reads': ('function h() internal view returns(uint256) { return gasleft(); } '
        'function run() external view returns(uint256) { return h()-h(); }',
        True, 'explicit evaluation-order support'),
    'nested-hidden-reads': ('function h() internal view returns(uint256) { return gasleft(); } '
        'function w() internal view returns(uint256) { return h(); } '
        'function run() external view returns(uint256) { return w()-w(); }',
        True, 'explicit evaluation-order support'),
    'two-yul-reads': ('function run() external view returns(uint256 r) '
        '{ assembly { r := sub(gas(),gas()) } }', True, 'explicit evaluation-order support'),
    'effectful-sibling-two-fields': ('uint256 a; uint256 b; '
        'function h() internal returns(uint256) { return a++; } '
        'function run() external returns(uint256) { return a+(gasleft()+h()); }',
        True, 'explicit evaluation-order support'),
    'default-off': ('function run() external view returns(uint256) { return gasleft(); }',
                    False, 'builtin call is outside the scalar slice'),
    'two-reads': ('function run() external view returns(uint256) { return gasleft()+gasleft(); }',
                  True, 'explicit evaluation-order support'),
    'increment-sibling': ('function h(uint256 a,uint256 b) internal pure returns(uint256) '
        '{ return a+b; } function run(uint256 n) external view returns(uint256) '
        '{ return h(gasleft(),n++); }', True, 'explicit evaluation-order support'),
    'effectful-helper': ('uint256 n; function h() internal returns(uint256) { return n++; } '
        'function run() external returns(uint256) { return gasleft()+h(); }',
        True, 'explicit evaluation-order support'),
    'virtual-helper': ('function h(uint256 a) internal pure virtual returns(uint256) '
        '{ return a; } function run() external view returns(uint256) { return gasleft()+h(1); }',
        True, 'explicit evaluation-order support'),
    'modifier-helper': ('modifier m() { _; } function h(uint256 a) internal pure m returns(uint256) '
        '{ return a; } function run() external view returns(uint256) { return gasleft()+h(1); }',
        True, 'explicit evaluation-order support'),
    'scalar-helper': ('function h(uint256 a) internal pure returns(uint256) { return a>1?a:1; } '
        'function run() external view returns(uint256) { return gasleft()+h(1); }', True, None),
}
CHECKS = '''
import Compiler.SolidityImport.SourceGasRunner
open Compiler Compiler.CompilationModel Compiler.CompilationModel.Denote
#eval match ECM.ExternalCallModule.compileCanonical (ECM.SourceGasRead.module "g" "1:1:0") {} [] with
  | .error "source gas observations require original bytecode; recompilation unsupported" => IO.println "compilation rejected"
  | _ => throw (IO.userError "source gas compilation was not rejected")
#eval match SolidityImport.SourceGasRunner.finish
    { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 } []
    { world := Verity.defaultState, bindings := [], sourceGas := some ⟨100000, [.endFrame 0]⟩ }
    [.ecm (ECM.LegacyVoidCall.module 1 []) []] with
  | .error "source gas transport requires an explicit call-boundary adapter" => IO.println "unmetered transport rejected"
  | _ => throw (IO.userError "unmetered transport was not rejected")
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    results = []
    for name, (body, enabled, reason) in CASES.items():
        (out / (name + '.sol')).write_text('pragma solidity 0.7.6; contract P { ' + body + ' }')
        driver = out / (name + '.lean')
        signature = {'increment-sibling': 'run(uint256)',
                     'two-calldata-copies': 'run(bytes,bytes)'}.get(name, 'run()')
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import model from {json.dumps(str(out))} entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none", '
            f'sourceGas := {str(enabled).lower()} }}\n  contract P\n  function {signature}\n')
        try:
            command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(),
                     '--timeout-ms', '180000'], log=out / (name + '.log'), timeout=210)
        except HarnessError:
            log = (out / (name + '.log')).read_text()
            if reason is None or '[solidity-import:unsupported]' not in log or reason not in log:
                raise HarnessError('wrong import rejection: ' + name + '\n' + log)
        else:
            if reason is not None:
                raise HarnessError('unsupported source gas import was accepted: ' + name)
        results.append({'case': name, 'diagnostic': reason})
    modern = out / 'ModernProfile.lean'
    modern.write_text('import Compiler.SolidityImport.Import\n'
        f'solidity_import model from {json.dumps(str(out))} entry "default-off.sol"\n'
        '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := none, '
        'bytecodeHash := "none", sourceGas := true }\n  contract P\n  function run()\n')
    try:
        command(['turbo-lean', 'eval', modern, '--project-dir', Path.cwd(),
                 '--timeout-ms', '180000'], log=out / 'modern.log', timeout=210)
    except HarnessError:
        if ': error: sourceGas requires the explicit Solidity 0.7.6 profile' not in (out / 'modern.log').read_text():
            raise HarnessError('modern profile did not reject with the expected diagnostic')
    else:
        raise HarnessError('source gas accepted outside the explicit legacy profile')
    results.append({'case': 'modern-profile', 'diagnostic': 'explicit Solidity 0.7.6 profile'})
    driver = out / 'RuntimeChecks.lean'
    driver.write_text(CHECKS)
    command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
            log=out / 'runtime.log', timeout=210)
    write_json(out / 'complete.json', {'imports': results, 'runtimeControls': 2})
    print(f'{len(results)} import boundaries and 2 runtime/compilation controls passed')


if __name__ == '__main__':
    main()
