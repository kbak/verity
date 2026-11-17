"""Keep non-scalar values and ambiguous storage references outside the legacy slice."""
import argparse
import json
from pathlib import Path
from eth_utils import keccak
from .engine import HarnessError, command, write_json
from .check_legacy_state_transitions import campaign, word, SENDER

CLASSIFIER = '''import Compiler.SolidityImport.LegacyStorageMembers
open Lean Compiler.CompilationModel.SolidityImport
private def typed (ty : String) : Json := Json.mkObj [("typeString", toJson ty)]
#eval show IO Unit from do
  let root := Json.mkObj [("stateVariable", toJson true),
    ("typeDescriptions", typed "struct P.Record"), ("typeName", Json.mkObj
      [("nodeType", toJson "UserDefinedTypeName"), ("referencedDeclaration", toJson (3 : Nat))])]
  let base := Json.mkObj [("nodeType", toJson "Identifier"),
    ("referencedDeclaration", toJson (2 : Nat)),
    ("typeDescriptions", typed "struct P.Record storage ref")]
  let member := Json.mkObj [("id", toJson (4 : Nat)), ("nodeType", toJson "VariableDeclaration"),
    ("name", toJson "flag"), ("typeDescriptions", typed "bool")]
  let decl := Json.mkObj [("nodeType", toJson "StructDefinition"), ("members", toJson #[member])]
  let env := { Env.init with
    stateVars := Env.init.stateVars.insert 2 root
    structs := Env.init.structs.insert 3 decl }
  let access := Json.mkObj [("nodeType", toJson "MemberAccess"), ("expression", base),
    ("referencedDeclaration", toJson (4 : Nat)), ("memberName", toJson "flag"),
    ("typeDescriptions", typed "bool")]
  unless legacyScalarStorageMember access env do throw (IO.userError "valid member rejected")
  for bad in [access.setObjVal! "referencedDeclaration" (toJson (5 : Nat)),
      access.setObjVal! "memberName" (toJson "other"),
      access.setObjVal! "typeDescriptions" (typed "uint8"),
      access.setObjVal! "expression" (base.setObjVal! "referencedDeclaration" (toJson (99 : Nat))),
      access.setObjVal! "expression" (base.setObjVal! "nodeType" (toJson "FunctionCall")),
      access.setObjVal! "expression" (base.setObjVal! "typeDescriptions"
        (typed "struct P.Record storage pointer"))] do
    if legacyScalarStorageMember bad env then throw (IO.userError "unbound member accepted")
  for ty in ["bool", "uint8", "uint160", "uint256", "address", "address payable", "bytes32",
      "int24", "bytes4", "uint7", "enum P.E", "struct P.Inner", "uint256[]", "bytes memory"] do
    let candidate := member.setObjVal! "typeDescriptions" (typed ty)
    let changed := decl.setObjVal! "members" (toJson #[candidate])
    let localEnv := { env with structs := env.structs.insert 3 changed }
    let expected := ["bool", "uint8", "uint160", "uint256", "address", "address payable",
      "bytes32"].contains ty
    unless legacyScalarStorageMember (access.setObjVal! "typeDescriptions" (typed ty)) localEnv ==
        expected do throw (IO.userError s!"wrong scalar admission: {ty}")
  unless !legacyScalarStorageMember access { env with stateVars := Env.init.stateVars } &&
      !legacyScalarStorageMember access { env with structs := Env.init.structs } do
    throw (IO.userError "missing declaration accepted")
  IO.println "legacy storage member classifier passed"
'''
HEADER = ('pragma solidity 0.7.6; interface I { function touch() external; } contract P { '
    'struct Inner { uint8 x; } struct Record { uint8 x; uint16 y; bool flag; int24 signedCanary; '
    'Inner inner; bytes4 tag; } Record value; Record sibling; Record[] records; '
    'mapping(uint256=>Record) table; uint256 marker; ')
# Positive fixtures omit nested and unsupported layout members; signed neighbors remain opaque.
SIMPLE = HEADER.replace('Inner inner; bytes4 tag;', '')
ROOT = 'function run(uint8 n) external returns(uint256) { '
CASES = {
    'read-write': (SIMPLE, 'value.x=n; return value.x;', None),
    'other-instance': (SIMPLE, 'sibling.y=n; value.x=n; return sibling.y;', None),
    'whole-copy': (SIMPLE, 'sibling=value; return 0;', 'does not support type struct'),
    'storage-alias': (SIMPLE, 'Record storage p=value; p.x=n; return p.x;', None),
    'memory-copy': (SIMPLE, 'Record memory p=value; return p.x;', 'storage copies to memory'),
    'nested': (HEADER, 'value.inner.x=n; return value.inner.x;', 'does not support type struct'),
    'array-path': (SIMPLE, 'records[0].x=n; return 0;', 'does not support type struct'),
    'mapping-path': (SIMPLE, 'table[n].x=n; return 0;', None),
    'mapping-memory-copy': (SIMPLE, 'Record memory p=table[n]; return p.x;',
                            'storage copies to memory'),
    'mapping-signed-key': (SIMPLE.replace('mapping(uint256=>Record)', 'mapping(int24=>Record)'),
                           'table[int24(n)].x=n; return 0;', 'signed mapping storage is outside'),
    'signed-read': (SIMPLE, 'return value.signedCanary==0 ? 1 : 0;', None),
    'signed-write': (SIMPLE, 'value.signedCanary=int24(n); return 0;', None),
    'fixed-bytes': (HEADER, 'value.tag=bytes4(uint32(n)); return 0;', 'memory structs require scalar fields'),
    'post-callback': (SIMPLE, 'I(address(1)).touch(); value.x=n; return 0;', None),
    'post-callback-read': (SIMPLE, 'I(address(1)).touch(); value.x+=n; return 0;',
                          'closed trailing continuation with storage-free operands'),
}


def mapping_scenario(kind, caller, layout, **_):
    """Check the original mapping write against independently computed physical slots."""
    base = int(next(item['slot'] for item in layout['storage'] if item['label'] == 'table'))
    keys = (0, 1, 17, 255)
    slots = {key: int.from_bytes(keccak(key.to_bytes(32, 'big') +
                                      base.to_bytes(32, 'big')), 'big') for key in keys}
    mask = (1 << 256) - 1
    # Keep packed neighbors, other keys, and unrelated state nonzero throughout.
    state = {int(item['slot']): mask for item in layout['storage']}
    state.update({slot: mask ^ (key << 16) for key, slot in slots.items()})
    state[9999] = 0xABCDE
    initial = [(caller, word(slot), word(value)) for slot, value in sorted(state.items())]
    calls, expected = [], {}
    for key in (*keys, 17, 0):
        ident = str(len(calls))
        state[slots[key]] = (state[slots[key]] & (mask ^ 255)) | key
        calls.append(dict(id=ident, label='run(uint8)', function='run', args=[key],
            sender=SENDER, target=caller, value='0x0',
            data='0x' + (keccak(text='run(uint8)')[:4] + key.to_bytes(32, 'big')).hex(),
            timestamp=1000000100 + len(calls), blockNumber=2 + len(calls)))
        expected[ident] = dict(status='ok', data=word(0), events=[],
            storage=[[caller, word(slot), word(value)] for slot, value in sorted(state.items())])
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    out=parser.parse_args().output.resolve()
    out.mkdir(parents=True,exist_ok=False)
    classifier=out/'Classifier.lean'
    classifier.write_text(CLASSIFIER)
    command(['turbo-lean','eval',classifier,'--project-dir','.', '--timeout-ms','180000'],
            log=out/'classifier.log',timeout=210)
    if 'legacy storage member classifier passed' not in (out/'classifier.log').read_text():
        raise HarnessError('member classifier did not execute')
    for name,(header,body,diagnostic) in CASES.items():
        (out/(name+'.sol')).write_text(header+ROOT+body+'} }')
        driver=out/(name+'.lean')
        driver.write_text('import Compiler.SolidityImport.Import\n'
            f'solidity_import imported from {json.dumps(str(out))} entry "{name}.sol"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", '
            'viaIR := false, optimizerRuns := none, bytecodeHash := "none" }\n'
            '  contract P\n  function run(uint8)\n')
        try:
            command(['turbo-lean','eval',driver,'--project-dir','.', '--timeout-ms','180000'],
                    log=out/(name+'.log'),timeout=210)
        except HarnessError:
            log=(out/(name+'.log')).read_text()
            if diagnostic is None or '[solidity-import:unsupported]' not in log or diagnostic not in log:
                raise HarnessError('wrong member rejection: '+name+'\n'+log)
        else:
            if diagnostic is not None:
                raise HarnessError('unsupported member shape accepted: '+name)
    # Admission alone is insufficient for a formerly rejected storage path.
    # Preserve its exact source and verify all three routes, with optimization off/on.
    for optimized in (False, True):
        if campaign(out / ('mapping-opt1' if optimized else 'mapping-opt0'),
                    kind='mapping-member', fixture=out / 'mapping-path.sol', contract='P',
                    functions=('run(uint8)',), prepared=True, optimized=optimized,
                    scenario_builder=mapping_scenario):
            raise HarnessError('mapping member physical storage observations differ')
    write_json(out/'complete.json',{'cases':list(CASES)})
    print('legacy storage member boundaries passed')


if __name__ == '__main__':
    main()
