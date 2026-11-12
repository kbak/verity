"""Raw static metadata and intentionally narrow legacy decoder admission."""
import argparse
import json
from pathlib import Path
from .engine import HarnessError, command, write_json

CLASSIFIER = '''import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.TransportBarriers
import Compiler.SolidityImport.RawStaticCallFrames
open Compiler Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
#eval show IO Unit from do
  let mod := ECM.SolidityRawStaticCall.module "ok"
  let args := List.replicate 4 (Expr.literal 0)
  unless closedTransportCovered mod args && isClosedStaticCall mod do
    throw (IO.userError "canonical raw static metadata rejected")
  unless (ECM.ExternalCallModule.compileCanonical mod {} (List.replicate 4 (.lit 0))).isOk do
    throw (IO.userError "canonical raw static compilation rejected")
  for bad in [{ mod with writesState := true }, { mod with readsState := false },
      { mod with summaryName := "forged" }, { mod with resultVars := ["another"] }] do
    unless !(closedTransportCovered bad args) && !isClosedStaticCall bad &&
        !(ECM.ExternalCallModule.compileCanonical bad {} []).isOk do
      throw (IO.userError "forged raw static metadata accepted")
  for count in [0, 3, 5] do
    unless !(closedTransportCovered mod (List.replicate count (.literal 0))) &&
        !(ECM.ExternalCallModule.compileCanonical mod {} (List.replicate count (.lit 0))).isOk do
      throw (IO.userError "wrong raw static arity accepted")
  IO.println "9 raw static structural boundaries passed"
'''
BODY = ('function run(address target) external view returns(uint256) { '
        '(bool ok,bytes memory data)=target.staticcall(abi.encodeWithSelector(0x12345678)); '
        'require(ok && data.length>=32); return abi.decode(data,(uint256)); }')
CASES = {
    'literal-selector': ('', BODY, None),
    'instance-selector': ('interface I { function f() external view returns(uint256); }',
        BODY.replace('0x12345678', 'I(target).f.selector'), 'type-qualified function'),
    'unresolved-immutables': ('',
        'address immutable first; address immutable second; '
        'constructor(address a,address b) { first=a; second=b; } ' +
        BODY.replace('target.staticcall(', 'first.staticcall('), 'requires a checked deployed binding'),
    'gas-option': ('', BODY.replace('target.staticcall(', 'target.staticcall{gas:100000}('),
                   'raw static call options'),
    'missing-bool': ('', BODY.replace('(bool ok,bytes memory data)', '(,bytes memory data)').replace(
        'require(ok && data.length>=32);', 'require(data.length>=32);'), 'requires a bool and memory bytes tuple'),
    'bool-decoder': ('', BODY.replace('return abi.decode(data,(uint256));',
        'bool answer=abi.decode(data,(bool)); return answer?1:0;'), 'requires one uint256 word'),
    'two-words': ('', BODY.replace('return abi.decode(data,(uint256));',
        '(uint256 a,uint256 b)=abi.decode(data,(uint256,uint256)); return a+b;'),
        'requires one uint256 word'),
    'v2': ('pragma abicoder v2;', BODY, 'raw static tuples require ABI coder v1'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    driver = out / 'Classifier.lean'
    driver.write_text(CLASSIFIER)
    command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
            log=out / 'classifier.log', timeout=210)
    if '9 raw static structural boundaries passed' not in (out / 'classifier.log').read_text():
        raise HarnessError('raw static structural checks did not complete')
    for name, (pragma, body, diagnostic) in CASES.items():
        (out / (name + '.sol')).write_text('pragma solidity 0.7.6; ' + pragma + ' contract P { ' + body + ' }')
        driver = out / (name + '.lean')
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import model from {json.dumps(str(out))} entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            '  contract P\n  function run(address)\n')
        try:
            command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
                    log=out / (name + '.log'), timeout=210)
        except HarnessError:
            log = (out / (name + '.log')).read_text()
            if diagnostic is None or '[solidity-import:unsupported]' not in log or diagnostic not in log:
                raise HarnessError('wrong raw static import rejection: ' + name + '\n' + log)
        else:
            if diagnostic is not None:
                raise HarnessError('unsupported raw static shape admitted: ' + name)
    write_json(out / 'complete.json', {'structuralCases': 9, 'importCases': len(CASES)})
    print(f'9 raw static structural and {len(CASES)} import boundaries passed')


if __name__ == '__main__':
    main()
