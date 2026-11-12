"""Original solc 0.7.6 gas-sensitive execution versus imported Denote.

No generated-bytecode equivalence is asserted: recompilation is rejected for
source gas observations. The local pinned EVM meters all original instructions;
Lean independently checks GAS and raw-call budgets while executing the model.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from eth_abi import encode

from .anvil import Anvil
from .engine import HarnessError, command, solc_compile, source_compiler, write_json
from .source_gas_trace import evidence, source_sites

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyGasObservations.sol')
MODEL = 'Contracts.SolidityImportSmoke.LegacyGasObservationsModel'
CHILDREN = [0x1234, 0x1235, 0x1236, 0x1237]
CODES = ['5a60005260206000f3', '5a60005260206000fd', 'fe', '']
MAX = (1 << 256) - 1


def address(value):
    return '0x' + value.to_bytes(20, 'big').hex()


def replay(out, payload, suffix='control', optimized=False):
    folder = out / suffix
    folder.mkdir(exist_ok=False)
    write_json(folder / 'input.json', payload)
    wrapper = folder / 'Run.lean'
    prefix = (Path(MODEL.replace('.', '/') + '.lean').read_text().replace(
        'optimizerRuns := none', 'optimizerRuns := some 200') if optimized else f'import {MODEL}\n')
    wrapper.write_text(prefix + '\n#eval main '
                       f'[{json.dumps(str(folder / "input.json"))}, '
                       f'{json.dumps(str(folder / "output.json"))}]\n')
    command(['turbo-lean', 'eval', wrapper, '--project-dir', Path.cwd(),
             '--timeout-ms', '180000'], log=folder / 'model.log', timeout=210)
    return json.loads((folder / 'output.json').read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--skip-build', action='store_true')
    parser.add_argument('--optimized', action='store_true')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    if not args.skip_build:
        command(['turbo-lean', '--json', 'build', MODEL,
                 'Contracts.SolidityImportSmoke.CallGasChecks'],
                log=out / 'build.log', timeout=1800)
    source = FIXTURE.read_text()
    request = {'language': 'Solidity', 'sources': {FIXTURE.name: {'content': source}},
               'settings': {'evmVersion': 'istanbul',
                            'optimizer': {'enabled': args.optimized, 'runs': 200},
                            'metadata': {'bytecodeHash': 'none'},
                            'outputSelection': {'*': {'*': ['evm.bytecode.object',
                                'evm.deployedBytecode.object', 'evm.deployedBytecode.sourceMap',
                                'evm.methodIdentifiers'], '': ['ast']}}}}
    release, solc = source_compiler({'solc': '0.7.6+commit.7338295f'})
    built = solc_compile(request, FIXTURE.parent, out / 'source', solc=solc)
    evm = built['contracts'][FIXTURE.name]['LegacyGasObservations']['evm']
    runtime = evm['deployedBytecode']['object']
    sites = source_sites(built['sources'][FIXTURE.name]['ast'])
    if not sites:
        raise HarnessError('fixture has no source gas observations')
    signatures = evm['methodIdentifiers']
    cases = [('observe()', [], []), ('ordered(bool)', ['bool'], [True]),
             ('ordered(bool)', ['bool'], [False])]
    for requested in [0, 1, 170000, 200000, MAX]:
        cases.append(('guarded(uint256)', ['uint256'], [requested]))
    run = 'run(address,uint256,uint256,bytes,bool,bool,bool)'
    types = ['address', 'uint256', 'uint256', 'bytes', 'bool', 'bool', 'bool']
    for delegated in [False, True]:
        for child in CHILDREN:
            for requested in [0, 1, 16, 17, 18, 10000, MAX]:
                cases.append((run, types, [address(child), 0, requested, b'',
                                           delegated, False, False]))
            for data in [b'', bytes(range(33)), bytes(range(129))]:
                for fail in [False, True]:
                    cases.append((run, types, [address(child), 0, 0, data,
                                               delegated, True, fail]))
    for amount in [1, 7, 1000001]:
        for requested in [0, 10000, MAX]:
            for child in CHILDREN:
                cases.append((run, types, [address(child), amount, requested, b'value',
                                           False, False, False]))
    for child in CHILDREN:
        cases.append(('assemblyGas(address)', ['address'], [address(child)]))
    for child in CHILDREN:
        cases.append(('twice(address)', ['address'], [address(child)]))
        for all_gas in [False, True]:
            cases.append(('forward(address,uint256,bool)', ['address', 'uint256', 'bool'],
                          [address(child), 10000, all_gas]))
    for child in CHILDREN:
        for operation in [0, 1]:
            for all_gas in [False, True]:
                for data in [b'', bytes(range(33)), bytes(range(129))]:
                    cases.append(('forwardData(address,bytes,uint8,uint256,bool)',
                        ['address', 'bytes', 'uint8', 'uint256', 'bool'],
                        [address(child), data, operation, 10000, all_gas]))
    transactions, expected, accounting_expected = [], [], []
    with Anvil(out / 'node') as node:
        sender = node.rpc('eth_accounts')[0]
        deployment = node.transact({'from': sender, 'data': '0x' + evm['bytecode']['object'],
                                   'gas': hex(10000000)})
        if deployment['receipt']['status'] != '0x1':
            raise HarnessError('gas fixture deployment failed')
        caller = deployment['receipt']['contractAddress']
        if node.rpc('eth_getCode', caller, 'latest') != '0x' + runtime:
            raise HarnessError('deployed source runtime differs from compiler output')
        node.rpc('anvil_setBalance', caller, hex(1000000))
        for child, code in zip(CHILDREN, CODES):
            node.rpc('anvil_setCode', address(child), '0x' + code)
            if node.rpc('eth_getCode', address(child), 'latest') != '0x' + code:
                raise HarnessError('independent gas child code installation differs')
        for index, (signature, types, values) in enumerate(cases):
            payload = encode(types, values)
            data = '0x' + signatures[signature] + payload.hex()
            record = node.transact({'from': sender, 'to': caller, 'data': data, 'gas': hex(200000)})
            txhash = record['receipt']['transactionHash']
            trace = node.rpc('debug_traceTransaction', txhash,
                             {'enableMemory': True, 'disableStack': False, 'disableStorage': True})
            write_json(out / 'node' / (txhash + '.gas.json'), trace)
            block = node.rpc('eth_getBlockByHash', record['receipt']['blockHash'], False)
            meter, gas_left, accounting = evidence(trace, record['call'], record['prestate'], runtime,
                                      evm['deployedBytecode']['sourceMap'], sites,
                                      coinbase=int(block['miner'], 16))
            transactions.append({'id': str(index), 'function': signature.split('(')[0],
                'args': [str(int.from_bytes(payload[i:i + 32], 'big')) for i in range(0, len(payload), 32)],
                'selector': str(int(signatures[signature], 16)), 'sender': str(int(sender, 16)),
                'target': str(int(caller, 16)), 'value': '0',
                'timestamp': str(int(block['timestamp'], 16)),
                'blockNumber': str(int(record['receipt']['blockNumber'], 16)),
                'observe': [[str(int(caller, 16)), '0']],
                'observeAccounts': [str(child) for child in CHILDREN], 'sourceGas': meter})
            status = 'ok' if record['receipt']['status'] == '0x1' else 'revert'
            if status == 'revert' and record['call'].get('error') != 'execution reverted':
                raise HarnessError('unsupported exceptional root outcome')
            accounting_expected.append({'id': str(index), 'events': accounting})
            def account_state(account, with_code=False):
                result = {'address': account,
                    'nonce': int(node.rpc('eth_getTransactionCount', account, 'latest'), 16),
                    'balance': int(node.rpc('eth_getBalance', account, 'latest'), 16)}
                if with_code:
                    result['code'] = node.rpc('eth_getCode', account, 'latest')
                return result
            expected.append({'deployment': {'creator': account_state(caller),
                'accounts': [account_state(address(child), True) for child in CHILDREN]},
                'id': str(index), 'status': status,
                'data': record['call'].get('output', '0x'),
                'nonce': int(node.rpc('eth_getStorageAt', caller, '0x0', 'latest'), 16),
                'sourceGasLeft': gas_left})
        initial = {'account': str(int(caller, 16)), 'storage': [['0', '0']],
                   'initialBalances': [[str(int(caller, 16)), '1000000']],
                   'accountNonce': '1',
                   'accountCode': [[str(child), '0x' + code] for child, code in zip(CHILDREN, CODES)],
                   'gasChildren': CHILDREN, 'transactions': transactions}
        write_json(out / 'node-provenance.json', node.provenance)
    write_json(out / 'input.json', initial)
    write_json(out / 'expected.json', expected)
    write_json(out / 'accounting-expected.json', accounting_expected)
    rows = replay(out, initial, optimized=args.optimized)
    if len(rows) != len(expected):
        raise HarnessError('model omitted source gas observations')
    for actual, want in zip(rows, expected):
        for key in ['id', 'status', 'data', 'sourceGasLeft', 'deployment']:
            if actual[key] != want[key]:
                raise HarnessError(f'{want["id"]}: {key}: {actual[key]} != {want[key]}')
        values = [row[2] for row in actual['storage'] if int(row[0], 16) == int(caller, 16) and int(row[1], 16) == 0]
        if len(values) != 1 or int(values[0], 16) != want['nonce']:
            raise HarnessError('source/model nonce or rollback differs')
    failures = {}
    controls = {'missing': 'original bytecode gas evidence missing',
        'site': 'source gas observation site differs',
        'truncated': 'unconsumed source gas evidence',
        'extra': 'unconsumed source gas evidence',
        'allowance': 'source child allowance differs from EIP-150 accounting',
        'target': 'source call request differs',
        'operand': 'source call request differs',
        'returned-gas': 'child returned gas above its allowance',
        'outcome': 'source child outcome differs from functional execution'}
    for name, diagnostic in controls.items():
        bad = copy.deepcopy(initial)
        index = next((i for i, tx in enumerate(initial['transactions'])
                      if any(e['type'] == 'call' and e['success'] for e in tx['sourceGas']['events'])), None)
        if index is None:
            raise HarnessError('missing successful call control')
        is_call = name in ('allowance', 'target', 'operand', 'returned-gas', 'outcome')
        bad['transactions'] = bad['transactions'][:index + 1 if is_call else 1]
        meter = bad['transactions'][-1]['sourceGas']
        if is_call:
            event = next(e for e in meter['events'] if e['type'] == 'call')
            key = {'allowance': 'allowance', 'target': 'target', 'operand': 'gas',
                   'returned-gas': 'gasLeft', 'outcome': 'success'}[name]
            event[key] = (not event[key] if name == 'outcome' else
                          event['allowance'] + 1 if name == 'returned-gas' else event[key] + 1)
        elif name == 'missing':
            del bad['transactions'][0]['sourceGas']
        elif name == 'site':
            meter['events'][0]['site'] = 'wrong-source-site'
        elif name == 'truncated':
            meter['events'].pop()
        else:
            meter['events'].append({'type': 'end', 'cost': 0})
        try:
            replay(out, bad, name, optimized=args.optimized)
        except HarnessError:
            log = (out / name / 'model.log').read_text()
            if ': error: ' + diagnostic not in log:
                raise HarnessError('wrong rejection or infrastructure failure: ' + name + '\n' + log)
            failures[name] = diagnostic
        else:
            raise HarnessError('malformed source gas evidence was accepted: ' + name)
    write_json(out / 'rejection-results.json', failures)
    write_json(out / 'complete.json', {'cases': len(rows), 'evidenceRejections': len(failures),
        'solc': release, 'optimized': args.optimized,
        'fixtureSha256': hashlib.sha256(source.encode()).hexdigest(), 'runtimeSha256': hashlib.sha256(bytes.fromhex(runtime)).hexdigest(),
        'head': command(['git', 'rev-parse', 'HEAD']).strip(),
        'workingTreeClean': not command(['git', 'status', '--porcelain']).strip(),
        'modelSha256': hashlib.sha256(Path(MODEL.replace('.', '/') + '.lean').read_bytes()).hexdigest(),
        'scope': 'finite original-bytecode/Denote evidence; trusted EVM span meter; no recompilation equivalence'})
    print(f'{len(rows)} original-bytecode gas cases and {len(failures)} malformed-evidence controls passed')


if __name__ == '__main__':
    main()
