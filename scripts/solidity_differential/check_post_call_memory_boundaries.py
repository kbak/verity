"""Keep post-call loop admission limited to storage-free, call-free memory work."""
import argparse
import json
from pathlib import Path
from .engine import HarnessError, command, write_json

CLASSIFIER = '''import Compiler.SolidityImport.TransportBarriers
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport
#eval show IO Unit from do
  let store := Stmt.mstore (.localVar "p") (.calldataload (.localVar "i"))
  let loop := fun body => Stmt.forEach "i" (.param "n") body
  let cases : List (String × Stmt × Bool) := [
    ("copy", loop [store], true),
    ("empty", loop [], true),
    ("nested", loop [loop [store]], true),
    ("branch", loop [.ite (.localVar "ok") [store] []], true),
    ("locals", loop [.letVar "a" (.mload (.literal 64)),
      .assignVar "a" (.add (.localVar "a") (.literal 1)), store], true),
    ("storage-bound", .forEach "i" (.storage "n") [store], false),
    ("transient-bound", .forEach "i" (.tload (.literal 0)) [store], false),
    ("storage-value", loop [.mstore (.literal 128) (.storage "n")], false),
    ("storage-pointer", loop [.mstore (.storage "n") (.literal 0)], false),
    ("storage-condition", loop [.ite (.storage "n") [store] []], false),
    ("nested-storage-read", loop [.letVar "x" (.mload (.storage "n"))], false),
    ("storage-write", loop [.setStorage "n" (.literal 1)], false),
    ("transient-write", loop [.tstore (.literal 0) (.literal 1)], false),
    ("nested-write", loop [loop [.setStorage "n" (.literal 1)]], false),
    ("raw-call", loop [.ecm (Compiler.ECM.SolidityRawCall.module "ok" false) []], false),
    ("nested-call", loop [loop [.ecm (Compiler.ECM.SolidityRawCall.module "ok" true) []]], false),
    ("gas-observation", loop [.ecm (Compiler.ECM.SourceGasRead.module "gas" "site") []], false),
    ("call-expression", loop [.letVar "x" (.externalCall "f" [])], false),
    ("event", loop [.emit "E" []], false),
    ("return", loop [.returnValues []], false),
    ("revert", loop [.revertEmpty], false),
    ("set-bit-loop", .forEachSetBit "i" (.literal 1) [store], false)]
  for (name, statement, expected) in cases do
    unless postCallMemoryStmt statement == expected && stmtAfterTrailingCall statement == expected do
      throw (IO.userError s!"wrong post-call loop verdict: {name}")
  IO.println s!"{cases.length} structural boundaries passed"
'''

CALL = 'bool ok; assembly { ok := call(1000000,a,0,0,0,0,0) } '
BODY = ('function run(address a,bytes calldata data) external returns(uint256) { ' + CALL +
        'return size(data); } function size(bytes memory data) internal pure returns(uint256) '
        '{ return data.length; }')
CASES = {
    'copy': (BODY, None),
    'storage-after-copy': (BODY.replace('return size(data);', 'uint256 n=size(data); return n+stored;'),
                           'closed trailing continuation with storage-free operands'),
    'loop-storage-write': ('function run(address a,bytes calldata data) external returns(uint256) { ' +
        CALL + 'for(uint256 i=0;i<2;i++) { stored=i; } return data.length; }',
        'closed trailing continuation with storage-free operands'),
    'loop-call': ('function run(address a,bytes calldata data) external returns(uint256) { ' +
        CALL + 'for(uint256 i=0;i<2;i++) { bool success; '
        'assembly { success := call(1000000,a,0,0,0,0,0) } } return data.length; }',
        'closed trailing continuation with storage-free operands'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    classifier = out / 'Classifier.lean'
    classifier.write_text(CLASSIFIER)
    command(['turbo-lean', 'eval', classifier, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
            log=out / 'classifier.log', timeout=210)
    results = []
    for name, (body, reason) in CASES.items():
        (out / (name + '.sol')).write_text('pragma solidity 0.7.6; contract P { uint256 stored; ' + body + ' }')
        driver = out / (name + '.lean')
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import model from {json.dumps(str(out))} entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            '  contract P\n  function run(address,bytes)\n')
        try:
            command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
                    log=out / (name + '.log'), timeout=210)
        except HarnessError:
            log = (out / (name + '.log')).read_text()
            if reason is None or '[solidity-import:unsupported]' not in log or reason not in log:
                raise HarnessError('wrong import rejection: ' + name + '\n' + log)
        else:
            if reason is not None:
                raise HarnessError('unsupported post-call effect admitted: ' + name)
        results.append({'case': name, 'diagnostic': reason})
    write_json(out / 'complete.json', {'structuralCases': 22, 'importCases': results})
    print('22 structural and 4 import boundaries passed')


if __name__ == '__main__':
    main()
