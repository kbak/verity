"""Preserve evaluation-order rejection for conflicting or unmodeled sibling effects."""
import argparse
import json
from pathlib import Path
from .engine import HarnessError, command, write_json

CLASSIFIER = '''import Compiler.SolidityImport.AssignmentOrder
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport
#eval show IO Unit from do
  let siblingRead := Expr.localVar "x"
  let safe := [Stmt.letVar "tmp" (.add siblingRead (.literal 1)), .assignVar "z" (.localVar "tmp")]
  unless localAssignmentSibling safe siblingRead &&
      localAssignmentSibling [.ite siblingRead safe [.panic .arithmeticOverflow]] siblingRead do
    throw (IO.userError "disjoint local prefix rejected")
  for pre in [[Stmt.assignVar "x" (.literal 1)], [.letVar "x" (.literal 1)],
      [.ite siblingRead safe [.assignVar "x" (.literal 1)]], [.setStorage "z" (.literal 1)],
      [.mstore (.literal 0) (.literal 1)], [.forEach "i" (.literal 1) safe],
      [.ecm (Compiler.ECM.SolidityRawCall.module "ok" false) []]] do
    unless !localAssignmentSibling pre siblingRead do
      throw (IO.userError "conflicting or unmodeled prefix accepted")
  for sibling in [Expr.storage "x", .add siblingRead (.literal 0), .tload (.literal 0)] do
    unless !localAssignmentSibling safe sibling do
      throw (IO.userError "nonlocal sibling accepted")
  IO.println "assignment structural boundaries passed"
'''
# All dynamic inputs are materialized helper bindings. Root params alone were
# already accepted by the older order-independent-atom rule.
CASES = {
    'left': ('require((z=x+y)>=x); return z;', None),
    'right': ('require(x<=(z=x+y)); return z;', None),
    'checked-left': ('require((z=x+y)>=x, "overflow"); return z;', None),
    'checked-right': ('require(x<=(z=x+y), "overflow"); return z;', None),
    'own-left': ('return (x=y)+x;', 'assignment operand with non-atomic sibling'),
    'own-right': ('return x+(x=y);', 'assignment operand with non-atomic sibling'),
    'nested-own': ('return (z=(x=y))+x;', 'assignment operand with non-atomic sibling'),
    'branch-own': ('return (z=(y>0 ? (x=y) : y))+x;', 'assignment operand with non-atomic sibling'),
    'two-effects': ('return (z=x)+(y=x);', 'assignment operand with non-atomic sibling'),
    'non-atomic': ('require((z=x+y)>=(x+1)); return z;', 'assignment operand with non-atomic sibling'),
    'storage-prefix': ('return (stored=y)+x;', 'assignment operand with non-atomic sibling'),
    'storage-sibling': ('return (z=y)+stored;', 'assignment operand with non-atomic sibling'),
    'multi-arg': ('return sum(z=x,y);', 'assignment expression in multi-argument call'),
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
    if 'assignment structural boundaries passed' not in (out/'classifier.log').read_text():
        raise HarnessError('assignment classifier did not execute')
    for name,(body,diagnostic) in CASES.items():
        modern = name.startswith('checked-')
        pragma = '0.8.34' if modern else '0.7.6'
        profile = ('{ evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, '
                   'bytecodeHash := "none" }') if modern else (
                   '{ solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
                   'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }')
        (out/(name+'.sol')).write_text(f'pragma solidity {pragma}; contract P {{ uint256 stored; '
            'function sum(uint256 x,uint256 y) internal pure returns(uint256) { return x+y; } '
            'function helper(uint256 x,uint256 y) internal returns(uint256) { uint256 z; x += 0; y += 0; '+body+' } '
            'function run(uint256 x,uint256 y) external returns(uint256) { return helper(x,y); } }')
        driver = out/(name+'.lean')
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import model from {json.dumps(str(out))} entry "{name}.sol"\n'
            f'  using {profile}\n'
            '  contract P\n  function run(uint256,uint256)\n')
        try:
            command(['turbo-lean','eval',driver,'--project-dir','.', '--timeout-ms','180000'],
                    log=out/(name+'.log'),timeout=210)
        except HarnessError:
            log = (out/(name+'.log')).read_text()
            if diagnostic is None or '[solidity-import:unsupported]' not in log or diagnostic not in log:
                raise HarnessError('wrong assignment rejection: '+name+'\n'+log)
        else:
            if diagnostic is not None:
                raise HarnessError('unsupported assignment shape accepted: '+name)
    write_json(out/'complete.json',{'cases':list(CASES)})
    print('assignment sibling boundaries passed')


if __name__ == '__main__':
    main()
