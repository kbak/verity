"""Observed general-loop storage and same-frame helpers against actual bytecode.

Canonical scalar ABI only. Every case compares physical storage as well as exact
return/revert bytes. Control-IR mutants require a clean baseline and completed
matching wrong outcomes in both mutated routes.
"""
import argparse
import hashlib
import json
from pathlib import Path

from eth_abi import encode
from eth_utils import keccak

from .anvil import Anvil
from .engine import HarnessError, SOLC, command, implementation_hashes, solc_compile, write_json

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyObservedStorage.sol')
DRIVER = Path('Contracts/SolidityImportSmoke/ObservedStorageChecks.lean')
MUTATIONS = ('helper-return-dropped', 'helper-return-exits-frame', 'storage-write-zero')


def cases():
    # Fixed compiler layout is asserted separately. Mapping addresses are the
    # Solidity keccak preimage, independent of the importer/model's slot logic.
    slots = list(range(5)) + [int.from_bytes(keccak(encode(['uint256', 'uint256'], [k, 5])), 'big')
                             for k in (0, 2)]
    initial = [7, 11] + [(123+i) * 2**128 + 5+i for i in range(3)] + [13, 17]
    rows = []

    def add(signature, args, values, state, returns=('uint256',), revert=False):
        types = signature.split('(', 1)[1][:-1].split(',')
        encoded = encode(types, args)
        data = (keccak(text='Error(string)')[:4] + encode(['string'], ['helper'])
                if revert else encode(returns, values))
        rows.append(dict(id=str(len(rows)), function=signature.split('(')[0], signature=signature,
            words=[str(int.from_bytes(encoded[i:i+32], 'big')) for i in range(0, len(encoded), 32)],
            calldata='0x' + (keccak(text=signature)[:4] + encoded).hex(),
            slots=list(map(str, slots)), initial=list(map(str, initial)),
            expected=dict(status='revert' if revert else 'ok', data='0x'+data.hex(),
                          storage=list(map(str, initial if revert else state)))))

    for n, stop, fail in [(0, 0, 0), (1, 0, 0), (4, 0, 0), (4, 2, 0),
                          (4, 2, 3), (4, 0, 3), (4, 2, 2)]:
        end = stop if 1 <= stop <= n else n
        state = initial.copy()
        state[0] += end*(end+1)//2
        state[1] += 100 + sum(i != 2 and i != stop for i in range(1, end+1))
        add('walk(uint256,uint256,uint256)', [n, stop, fail], [end], state,
            revert=1 <= fail <= end)
    for n in (0, 1, 3):
        state = initial.copy(); state[0] += n; state[1] += n+10*(n-int(n >= 2))
        add('nested(uint256)', [n], [state[0]], state)
    for index, delta, n in [(0, 2, 0), (1, 2, 1), (2, 3, 3), (0, 2**128-1, 3)]:
        state = initial.copy(); low = (5+index+delta*min(n, 2)) % 2**128
        state[2+index] = (123+index)*2**128+low; state[1] += 100
        add('record(uint256,uint128,uint256)', [index, delta, n], [low, index+1], state,
            returns=('uint256', 'uint256'))
    for key, n in [(0, 0), (0, 3), (2, 2)]:
        state = initial.copy(); index = 5+(key == 2); state[index] += n; state[1] += 100
        add('mappingLoop(uint256,uint256)', [key, n], [state[index]], state)
    for index in (0, 1, 2):
        state = initial.copy(); state[2+index] += 2
        add('capture(uint256)', [index], [7+index, index+1], state,
            returns=('uint256', 'uint256'))
    for n, stop in [(0, 0), (4, 2), (3, 0)]:
        end = stop if 1 <= stop <= n else n
        state = initial.copy(); state[0] += end*(end+1)//2; state[1] += 100
        add('voidLoop(uint256,uint256)', [n, stop], [state[0]], state)
    for n, fail in [(0, 0), (3, 0), (3, 1)]:
        state = initial.copy(); state[0] += 10+min(n, 1); state[1] += 1007
        add('through(uint256,uint256)', [n, fail], [min(n, 1)], state,
            revert=n > 0 and fail == 1)
    for limit in (6, 7, 10):
        state = initial.copy(); state[0] = max(7, limit)
        add('stateBound(uint256)', [limit], [state[0]], state)
    return rows


def identity(fixture=FIXTURE):
    return implementation_hashes() | {
        str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in (fixture, DRIVER)}


def check(output, optimized=False, mutation=None, ordinary_import=False, spec=None):
    spec = spec or {}
    fixture = spec.get('fixture', FIXTURE)
    contract = spec.get('contract', 'LegacyObservedStorage')
    output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=False)
    captured = identity(fixture); source = fixture.read_text()
    write_json(output/'manifest.json', dict(implementation=captured,
        solcSha256={str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in (SOLC, Path('.lake/solidity-import/solc-0.7.6'))}))
    result = solc_compile({'language': 'Solidity', 'sources': {'Source.sol': {'content': source}},
        'settings': {'evmVersion': 'istanbul', 'optimizer': {'enabled': optimized, 'runs': 800},
            'metadata': {'bytecodeHash': 'none'}, 'outputSelection': {'*': {'': ['ast'],
                '*': ['storageLayout', 'evm.bytecode.object', 'evm.methodIdentifiers']}}}},
        output, output/'source-solc', solc=Path.cwd()/'.lake/solidity-import/solc-0.7.6')
    ast = result['sources']['Source.sol']['ast']
    declaration = next(n for n in ast['nodes'] if n['nodeType'] == 'ContractDefinition')
    source_artifact = result['contracts']['Source.sol'][contract]
    layout = source_artifact['storageLayout']
    expected_layout = spec.get('layout', [
        ('total', '0', 0), ('afterCalls', '1', 0), ('records', '2', 0), ('values', '5', 0)])
    if [(n['label'], n['slot'], n['offset']) for n in layout['storage']] != expected_layout:
        raise HarnessError('fixture layout changed')
    functions = [n for n in declaration['nodes'] if n['nodeType'] == 'FunctionDefinition'
                 and n['visibility'] == 'external']
    rows = spec.get('cases', cases)()
    write_json(output/'input.json', dict(source=source, ast=ast, layout=layout, functions=functions,
        cases=rows, bases=declaration['linearizedBaseContracts'], mutation=mutation or ''))
    driver = output/'Driver.lean'
    if ordinary_import:
        from .observed_import import write_driver
        write_driver(driver, DRIVER.read_text(), output, source, rows, optimized, True, spec)
    else:
        driver.write_text(DRIVER.read_text()+'\nobserved_storage_cases '+
            json.dumps(str(output/'input.json'))+' output '+json.dumps(str(output/'model.json'))+'\n')
    command(['turbo-lean', '--json', 'eval', driver, '--project-dir', '.', '--timeout-ms', '180000'],
            timeout=240, log=output/'model.log')
    model = json.loads((output/'model.json').read_text())
    if ordinary_import:
        from .observed_import import validate_metadata
        validate_metadata(model, optimized, True, {row['function'] for row in rows}, spec)
    expected_rejections = ([sig.split('(')[0] for sig, _ in spec['negatives']] if spec
                           else ['ambiguousRecord', 'recursive'])
    if (model['rejected'] != expected_rejections
            or len(model['observations']) != len(rows)
            or {r['id'] for r in rows} != {r['id'] for r in model['observations']}):
        raise HarnessError('observed storage coverage differs')
    models = {r['id']: {k: r[k] for k in ('status', 'data', 'storage')} for r in model['observations']}
    signatures = {r['function']: r['signature'] for r in rows}
    arms = ['case 0x'+source_artifact['evm']['methodIdentifiers'][signatures[f['name']]]+
            ' {\n'+f['body']+'\n}' for f in model['compiled']]
    yul = ('object "Observed" { code { datacopy(0, dataoffset("runtime"), datasize("runtime")) '
           'return(0, datasize("runtime")) } object "runtime" { code { '
           'switch shr(224, calldataload(0))\n'+'\n'.join(arms)+
           '\ndefault { revert(0, 0) } } } }')
    (output/'observed.yul').write_text(yul)
    generated = solc_compile({'language': 'Yul', 'sources': {'Observed.yul': {'content': yul}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': optimized, 'runs': 800},
                    'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}},
        output, output/'generated-solc')['contracts']['Observed.yul']['Observed']
    observations, failures, witnesses = [], [], []
    with Anvil(output/'node') as node:
        sender = node.rpc('eth_accounts')[0]; accounts = {}
        for route, artifact in [('source', source_artifact), ('generated', generated)]:
            trace = node.transact({
                'from': sender, 'data': '0x'+artifact['evm']['bytecode']['object'], 'gas': hex(4000000)})
            if trace['receipt']['status'] != '0x1': raise HarnessError('deployment failed')
            accounts[route] = trace['receipt']['contractAddress']
        for row in rows:
            observed = dict(case=row, model=models[row['id']])
            for route, account in accounts.items():
                for slot, word in zip(row['slots'], row['initial']):
                    node.rpc('anvil_setStorageAt', account, hex(int(slot)), '0x'+int(word).to_bytes(32,'big').hex())
                trace = node.transact({'from': sender, 'to': account, 'data': row['calldata'],
                                       'gas': hex(500000)})
                call = trace['call']; success = trace['receipt']['status'] == '0x1'
                if not success and call.get('error') != 'execution reverted':
                    raise HarnessError(f'{route}: non-source failure {call.get("error")}')
                observed[route] = dict(status='ok' if success else 'revert', data=call.get('output','0x'),
                    storage=[str(int(node.rpc('eth_getStorageAt', account, hex(int(s)),
                        trace['receipt']['blockNumber']), 16)) for s in row['slots']])
            if observed['source'] != row['expected']: failures.append(row['id'])
            elif mutation:
                if observed['model'] == observed['generated'] and observed['model'] != row['expected']:
                    witnesses.append(row['id'])
            elif observed['model'] != row['expected'] or observed['generated'] != row['expected']:
                failures.append(row['id'])
            observations.append(observed)
    if identity(fixture) != captured: raise HarnessError('implementation changed during storage checks')
    passed = not failures and (not mutation or bool(witnesses))
    write_json(output/'results.json', dict(passed=passed, failures=failures, mutation=mutation,
        completedMutationWitnesses=witnesses, optimized=optimized, observations=observations))
    if not passed: raise HarnessError('storage/helper correspondence or mutation sensitivity failed')
    print('observed storage/helper checks passed')


def run(output, optimized=False, mutation=None, ordinary_import=False):
    if not mutation: return check(output, optimized, ordinary_import=ordinary_import)
    output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=False)
    check(output/'baseline', optimized, ordinary_import=ordinary_import)
    check(output/'mutant', optimized, mutation, ordinary_import)
    if ((output/'baseline/manifest.json').read_bytes() != (output/'mutant/manifest.json').read_bytes()):
        raise HarnessError('mutation baseline identity changed')
    result = json.loads((output/'mutant/results.json').read_text())
    write_json(output/'results.json', dict(result, baselinePassed=True))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--ordinary-import', action='store_true')
    parser.add_argument('--mutation', choices=MUTATIONS)
    run(**vars(parser.parse_args()))
