"""Compare field-value snapshots, storage writes and index failures with original bytecode."""
import argparse
from pathlib import Path

from eth_abi import encode
from eth_utils import keccak

from .anvil import Anvil
from .check_interval_progress_interface import evaluate
from .engine import HarnessError, command, solc_compile, source_compiler

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyRecordSnapshots.sol')
SIGNATURE = 'scan(uint256,uint256,uint256,uint256,int56)'
WORD = 1 << 256
MASK56 = (1 << 56) - 1
TYPES = ['uint32', 'int56', 'bool', 'uint256']
ROWS = [(13, -(1 << 55), True, WORD - 69), (29, (1 << 55) - 1, True, 23),
        (65, -92, False, 1 << 245)]
CASES = [(0, 3, 7), (1, 3, -11), (3, 3, -1), (4, 3, -16), (7, 2, -7), (2, 1, 42)]


def word(n):
    return '0x' + n.to_bytes(32, 'big').hex()


def packed(key, signed, boolean):
    return (0xDEADBEEF << 96) + (int(boolean) << 88) + ((signed & MASK56) << 32) + key


def import_cmd(directory):
    return f'''solidity_import copied from "{directory}" entry "{FIXTURE.name}"
  using {{ solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,
          optimizerRuns := some 800, bytecodeHash := "none" }}
  interval contract LegacyRecordSnapshots
  function {SIGNATURE}
  loop "{FIXTURE.name}" line 20 column 9
'''


def identifier(ast, label):
    if isinstance(ast, dict):
        if ast.get('nodeType') == 'VariableDeclaration' and ast.get('name') == label:
            return ast['id']
        nodes = ast.values()
    elif isinstance(ast, list):
        nodes = ast
    else:
        return None
    return next((value for n in nodes if (value := identifier(n, label)) is not None), None)


def compare_source(output):
    _, solc = source_compiler({'solc': '0.7.6+commit.7338295f'})
    request = dict(language='Solidity', sources={FIXTURE.name: {'content': FIXTURE.read_text()}},
                   settings={'evmVersion': 'istanbul', 'optimizer': {'enabled': True, 'runs': 800},
                             'metadata': {'bytecodeHash': 'none'},
                             'outputSelection': {'*': {'': ['ast'],
                                 '*': ['storageLayout', 'evm.deployedBytecode.object']}}})
    result = solc_compile(request, FIXTURE.parent, output / 'original', solc)
    artifact = result['contracts'][FIXTURE.name][FIXTURE.stem]
    layout = artifact['storageLayout']['storage']
    base = int(next(row['slot'] for row in layout if row['label'] == 'rows'))
    storage = {base-1: 0xBEEF}
    for i, (key, delta, ready, payload) in enumerate(ROWS):
        storage[base+2*i] = packed(key, delta, 0x7f if i == 1 else ready)
        storage[base+2*i+1] = payload
    address = '0x' + '12'*20
    cases = []
    with Anvil(output / 'evm', hardfork='istanbul') as node:
        sender = node.rpc('eth_accounts')[0]
        node.rpc('anvil_setCode', address, '0x'+artifact['evm']['deployedBytecode']['object'])
        for i, (middle, count, replacement) in enumerate(CASES + [(3, 4, 17), (2, 4, 17), (0, 0, 17)]):
            for slot, value in storage.items():
                node.rpc('anvil_setStorageAt', address, word(slot), word(value))
            args = [middle, middle, middle, count, replacement]
            data = keccak(text=SIGNATURE)[:4] + encode(['uint256']*4 + ['int56'], args)
            record = node.transact({'from': sender, 'to': address, 'data': '0x'+data.hex(),
                                    'gas': hex(1_000_000), 'gasPrice': hex(2_000_000_000)})
            row = node.observe(record, str(i), [(address, word(k)) for k in storage])
            actual = {int(slot,16): int(value,16) for acct,slot,value in row['storage']
                      if acct.lower() == address}
            if count == 0 or middle % count >= len(ROWS) or (middle + 1) % count >= len(ROWS):
                if row['status'] != 'invalid' or actual != storage:
                    raise HarnessError(f'expected legacy INVALID on case {args}')
                continue
            first_index, second_index = middle % count, (middle + 1) % count
            first, second = ROWS[first_index], ROWS[second_index]
            original = storage[base+2*first_index]
            updated = (original & ~(MASK56 << 32)) | ((replacement & MASK56) << 32)
            if first_index == second_index:
                second = (second[0], replacement, second[2], second[3])
            expected = b''.join(keccak(encode(TYPES, r)) for r in [first, second])
            post = dict(storage)
            post[base+2*first_index] = updated
            if row['status'] != 'ok' or row['data'] != '0x'+expected.hex() or actual != post:
                raise HarnessError(f'original Solidity snapshot mismatch on {args}')
            scalar_values = [int(n) % WORD for r in (first, second) for n in r]
            cases.append((middle, count, replacement % WORD, scalar_values, list(post.values())))
    ast = result['sources'][FIXTURE.name]['ast']
    return storage, cases, [identifier(ast, n) for n in ('first', 'second')]


def model_checks(output, storage, cases, ids):
    if any(i is None for i in ids):
        raise HarnessError('missing snapshot destination declarations')
    src = 'import Compiler.SolidityImport.IntervalCommand\nimport Compiler.SolidityImport.Differential\n'
    src += 'open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport Denote\n'
    src += import_cmd(FIXTURE.parent) + f'''
def words : List (Nat × Nat) := [{", ".join(f"({k}, {n})" for k,n in storage.items())}]
def zeros : List (String × Nat) := copied.site.structLocals.flatMap fun (_, members) =>
  members.map fun (_, _, name) => (name, 0)
def frame (middle count replacement : Nat) : DenoteState := {{
  world := words.foldl (fun w kv => w.writePhysicalSlot kv.1 (Verity.Core.Uint256.ofNat kv.2))
    Verity.defaultState
  bindings := [(copied.site.lowName, middle), (copied.site.highName, middle),
    ("target", middle), ("count", count), ("replacement", replacement)] ++ zeros }}
def read (middle count replacement : Nat) (p : CertifiedInterval.Site := copied.site) :
    Option (List Nat × List Nat) := do
  let .halt (.ok (.continue s)) := p.step Differential.oracle
      (frame middle count replacement) | none
  let first ← p.snapshot? s {ids[0]}
  let second ← p.snapshot? s {ids[1]}
  return ((first ++ second).map Prod.snd, words.map fun (slot, _) => (s.world.storage slot).val)
partial def fault (alias : Bool) (redirect : List (String × String)) : Stmt → Stmt
  | .ite c yes no => .ite c (yes.map (fault alias redirect)) (no.map (fault alias redirect))
  | .assignVar name rhs => .assignVar (if alias then (redirect.lookup name).getD name else name) rhs
  | .letVar name (.signextend width value) =>
    .letVar name (if alias then .signextend width value else value)
  | st => st
def completedWrong (alias : Bool) : Bool := Id.run do
  let bindings (id : Nat) := ((copied.site.structLocals.lookup id).getD []).map (·.2.2)
  let redirect := (bindings {ids[1]}).zip (bindings {ids[0]})
  let bad := {{ copied.site with body := copied.site.body.map (fault alias redirect) }}
  let some (before, _) := read 2 1 42 | return false
  let some (after, _) := read 2 1 42 bad | return false
  return before != after
#guard completedWrong true
#guard completedWrong false
#guard copied.site.snapshotRecords.length == 2
#guard copied.site.nonzeroInputs == ["count"]
'''
    for middle, count, repl, fields, slots in cases:
        src += f'#guard read {middle} {count} {repl} == some ({fields}, {slots})\n'
    src += '''#guard (match copied.site.step Differential.oracle (frame 3 4 17) with
  | .halt (.ok .invalid) => true | _ => false)
#guard (match copied.site.step Differential.oracle (frame 2 4 17) with
  | .halt (.ok .invalid) => true | _ => false)
#guard (match copied.site.step Differential.oracle (frame 0 0 17) with
  | .halt (.error _) => true | _ => false)
'''
    driver = output / 'Snapshots.lean'
    driver.write_text(src)
    evaluate(driver, output / 'projected.json')


def rejections(output):
    src = FIXTURE.read_text()
    controls = {
        'alias': src.replace('uint256 middle;', 'uint256 middle; Row memory old = first;')
                    .replace('abi.encode(first.key', 'abi.encode(old.key'),
        'escape': src.replace('        return (keccak256',
                              '        Row memory aliasToOld = first;\n        return (keccak256'),
        'allocator': src.replace('        return (keccak256',
                                 '        assembly { pop(mload(0x40)) }\n        return (keccak256'),
    }
    for label, source in controls.items():
        project = output / label
        project.mkdir(exist_ok=True)
        (project / FIXTURE.name).write_text(source)
        driver = project / 'Reject.lean'
        driver.write_text('import Compiler.SolidityImport.IntervalCommand\n' + import_cmd(project))
        reason = ('struct local initializer must be a supported struct' if label == 'alias' else
                  'independent local destinations and unobservable memory addresses')
        evaluate(driver, project / 'diagnostic.json', rejection=reason)
    unstable = output / 'changing-divisor'
    unstable.mkdir(exist_ok=True)
    (unstable / FIXTURE.name).write_text(src.replace('            first = rows',
        '            count = count + 1;\n            first = rows'))
    driver = unstable / 'Reject.lean'
    driver.write_text('import Compiler.SolidityImport.IntervalCommand\n' + import_cmd(unstable))
    evaluate(driver, unstable / 'diagnostic.json', rejection='stable scalar divisors')
    guarded = output / 'ordinary'
    guarded.mkdir(exist_ok=True)
    (guarded / FIXTURE.name).write_text(src.replace('% count', '% 3').replace('            first = rows',
        '            if (middle <= low || middle >= high) break;\n            first = rows'))
    driver = guarded / 'Reject.lean'
    bounded = import_cmd(guarded).replace('interval contract', 'contract').split('  loop ')[0]
    driver.write_text('import Compiler.SolidityImport.Import\n' + bounded)
    evaluate(driver, guarded / 'diagnostic.json', rejection='memory struct writes and rebinding')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    output = parser.parse_args().output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.IntervalCommand',
             'Compiler.SolidityImport.Differential', '--project-dir', '.'], timeout=600)
    model_checks(output, *compare_source(output))
    rejections(output)
