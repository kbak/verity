"""Closed static queries may follow callbacks; direct storage reads and forged effects may not."""
import argparse
import json
from pathlib import Path
from .engine import HarnessError, command, write_json

CLASSIFIER = '''import Compiler.SolidityImport.TransportBarriers
import Compiler.SolidityImport.Coverage
open Compiler Compiler.CompilationModel Compiler.CompilationModel.SolidityImport
#eval show IO Unit from do
  let raw := ECM.SolidityRawStaticCall.module "ok"
  let args := List.replicate 4 (Expr.literal 0)
  let query := Stmt.ecm raw args
  let callback := Stmt.ecm (ECM.SolidityRawCall.module "ok" false) []
  let typed := Stmt.ecm (ECM.LegacyBoolCall.module "ok" 1234 1)
    [.localVar "target", .localVar "account"]
  for read in [query, typed, .setStorage "slot" (.literal 1),
      .ite (.localVar "flag") [query] [typed]] do
    unless stmtAfterTrailingCall read && onlyTrailingLowLevelCallWindows [callback, read] do
      throw (IO.userError "closed static continuation rejected")
  for bad in [{ raw with writesState := true }, { raw with readsState := false },
      { raw with summaryName := "forged" }, { raw with resultVars := ["another"] }] do
    unless !stmtAfterTrailingCall (.ecm bad args) do
      throw (IO.userError "forged static descriptor accepted")
  for read in [Stmt.ecm raw [.storage "target"],
      .ecm raw [.add (.literal 0) (.tload (.literal 0))],
      .setStorage "slot" (.storage "other"), .letVar "n" (.storage "slot"),
      .setStorageAddr "address" (.literal 1),
      .setStorageArrayElement "items" (.literal 0) (.literal 1),
      .forEach "i" (.literal 2) [.setStorage "slot" (.literal 1)],
      .tstore (.literal 0) (.literal 1), .letVar "t" (.tload (.literal 0)),
      .forEach "i" (.literal 2) [query], .forEach "i" (.literal 2) [typed]] do
    unless !stmtAfterTrailingCall read &&
        !onlyTrailingLowLevelCallWindows [callback, query, read] do
      throw (IO.userError "post-call storage or loop interaction accepted")
  IO.println "post-call static structural boundaries passed"
'''
CALL = 'bool success; assembly { success := call(1000000,callback,0,0,0,0,0) } '
QUERY = ('(bool ok, bytes memory data) = target.staticcall(abi.encodeWithSelector(0x12345678)); '
         'require(ok && data.length>=32); return abi.decode(data,(uint256));')
HEADER = 'function run(address callback,address target) external returns(uint256) { '
CASES = {
    'raw-read': (HEADER + CALL + QUERY + '}', None),
    'typed-bool': (HEADER + CALL + 'return I(target).query(address(this)) ? 1 : 0; }', None),
    'captured-target': (HEADER + 'target=stored; ' + CALL + QUERY + '}', None),
    'read-target': (HEADER + CALL + 'target=stored; ' + QUERY + '}',
                    'closed trailing continuation with storage-free operands'),
    'storage-after-query': (HEADER + CALL + QUERY.replace('return abi.decode(data,(uint256));',
        'return abi.decode(data,(uint256))+count;') + '}', 'closed trailing continuation with storage-free operands'),
    'write-after-query': (HEADER + CALL + QUERY.replace('return abi.decode(data,(uint256));',
        'count=1; return abi.decode(data,(uint256));') + '}', None),
    'mapping-write': (HEADER + CALL + 'cells[0]=1; return 0; }',
        'closed trailing continuation with storage-free operands'),
    'array-write': (HEADER + CALL + 'fixedValues[0]=1; return 0; }',
        'does not support type uint256[2] storage ref'),
    'write-storage-rhs': (HEADER + CALL + QUERY.replace('return abi.decode(data,(uint256));',
        'count=count+1; return abi.decode(data,(uint256));') + '}',
        'closed trailing continuation with storage-free operands'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    out = parser.parse_args().output.resolve()
    out.mkdir(parents=True,exist_ok=False)
    classifier = out/'Classifier.lean'
    classifier.write_text(CLASSIFIER)
    command(['turbo-lean','eval',classifier,'--project-dir','.', '--timeout-ms','180000'],
            log=out/'classifier.log',timeout=210)
    if 'post-call static structural boundaries passed' not in (out/'classifier.log').read_text():
        raise HarnessError('post-call classifier did not execute')
    for name,(body,diagnostic) in CASES.items():
        (out/(name+'.sol')).write_text('pragma solidity 0.7.6; '
            'interface I { function query(address a) external view returns(bool); } '
            'contract P { address stored; uint256 count; mapping(uint256=>uint256) cells; '
            'uint256[2] fixedValues; '+body+' }')
        driver = out/(name+'.lean')
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import model from {json.dumps(str(out))} entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            '  contract P\n  function run(address,address)\n')
        try:
            command(['turbo-lean','eval',driver,'--project-dir','.', '--timeout-ms','180000'],
                    log=out/(name+'.log'),timeout=210)
        except HarnessError:
            log = (out/(name+'.log')).read_text()
            if diagnostic is None or '[solidity-import:unsupported]' not in log or diagnostic not in log:
                raise HarnessError('wrong post-call rejection: '+name+'\n'+log)
        else:
            if diagnostic is not None:
                raise HarnessError('unsupported post-call shape accepted: '+name)
    write_json(out/'complete.json',{'cases':list(CASES)})
    print('post-call static boundaries passed')


if __name__ == '__main__':
    main()
