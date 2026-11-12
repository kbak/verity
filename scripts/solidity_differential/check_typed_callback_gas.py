"""Original-bytecode gas for ABI-v1 callbacks, including terminal reverts."""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from eth_abi import encode
from .anvil import Anvil
from .engine import HarnessError, command, solc_compile, source_compiler, write_json
from .source_gas_trace import evidence, source_sites

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyTypedCallGas.sol')
MODEL = Path('Contracts/SolidityImportSmoke/LegacyTypedCallGasModel.lean')
CHILDREN = [0x1234, 0x1235, 0x1236, 0x3344]
CODES = ['5a60005260206000f3', '5a60005260206000fd', 'fe', '']
BALANCE = 1000000


def address(n):
    return '0x' + n.to_bytes(20, 'big').hex()


def replay(out, payload, optimized, *, model=None):
    out.mkdir(exist_ok=False)
    write_json(out / 'input.json', payload)
    code = (model or MODEL).read_text()
    if optimized:
        code = code.replace('optimizerRuns := none', 'optimizerRuns := some 200')
    driver = out / 'Run.lean'
    driver.write_text(code + '\n#eval main ' + json.dumps(
        [str(out / 'input.json'), str(out / 'output.json')]) + '\n')
    command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
            log=out / 'model.log', timeout=210)
    return json.loads((out / 'output.json').read_text())


def check_rejections(out, initial, optimized):
    # The first successful run reaches before-call, payment, and after-call.
    chosen = next(i for i, tx in enumerate(initial['transactions'])
                  if sum(e['type'] == 'call' for e in tx['sourceGas']['events']) == 3)
    controls = {
        'missing': 'original bytecode gas evidence missing',
        'site': 'source gas observation site differs',
        'missing-read': 'missing or reordered source gas observation',
        'swapped-read-call': 'missing or reordered source gas observation',
        'missing-call': 'source call request differs',
        'target': 'source call request differs',
        'operand': 'source call request differs',
        'allowance': 'source child allowance differs from EIP-150 accounting',
        'returned-gas': 'child returned gas above its allowance',
        'outcome': 'source child outcome differs from functional execution',
        'returndata': 'source child outcome differs from functional execution',
        'truncated': 'unconsumed source gas evidence',
        'extra': 'unconsumed source gas evidence',
        'revert-tail': 'unconsumed source gas evidence',
    }
    results = {}
    for name, diagnostic in controls.items():
        bad = copy.deepcopy(initial)
        index = chosen
        if name == 'revert-tail':
            index = next(i for i, tx in enumerate(initial['transactions']) if any(
                e['type'] == 'call' and not e['success'] for e in tx['sourceGas']['events']))
        bad['transactions'] = bad['transactions'][:index + 1]
        tx = bad['transactions'][-1]
        events = tx['sourceGas']['events']
        call_index = next(i for i, e in enumerate(events) if e['type'] == 'call')
        read_index = call_index - 1
        if events[read_index]['type'] != 'read':
            raise HarnessError('typed call control lacks its implicit GAS')
        event = events[call_index]
        if name == 'missing':
            del tx['sourceGas']
        elif name == 'site':
            events[read_index]['site'] = 'wrong-callback-site'
        elif name == 'missing-read':
            events.pop(read_index)
        elif name == 'swapped-read-call':
            events[read_index], events[call_index] = events[call_index], events[read_index]
        elif name == 'missing-call':
            events.pop(call_index)
        elif name in ('truncated', 'revert-tail'):
            events.pop()
        elif name == 'extra':
            events.append({'type': 'end', 'cost': 0})
        elif name == 'returned-gas':
            event['gasLeft'] = event['allowance'] + 1
        elif name == 'outcome':
            event['success'] = not event['success']
        elif name == 'returndata':
            event['returndata'] = event['returndata'] + [1]
        else:
            key = {'target': 'target', 'operand': 'gas', 'allowance': 'allowance'}[name]
            event[key] += 1
        folder = out / ('reject-' + name)
        try:
            replay(folder, bad, optimized)
        except HarnessError:
            log = (folder / 'model.log').read_text()
            if ': error: ' + diagnostic not in log:
                raise HarnessError('wrong rejection or instrumentation failure: ' + name + '\n' + log)
        else:
            raise HarnessError('malformed callback evidence accepted: ' + name)
        results[name] = diagnostic
    write_json(out / 'rejections.json', results)
    return len(results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    if not args.skip_build:
        command(['turbo-lean', '--json', 'build', 'Contracts.SolidityImportSmoke.LegacyTypedCallGasModel'],
                log=out / 'build.log', timeout=1800)
    source = FIXTURE.read_text()
    request = {'language': 'Solidity', 'sources': {FIXTURE.name: {'content': source}}, 'settings': {
        'evmVersion': 'istanbul', 'optimizer': {'enabled': args.optimized, 'runs': 200},
        'metadata': {'bytecodeHash': 'none'}, 'outputSelection': {'*': {'*': ['evm.bytecode.object',
            'evm.deployedBytecode.object', 'evm.deployedBytecode.sourceMap', 'evm.methodIdentifiers'],
            '': ['ast']}}}}
    release, solc = source_compiler({'solc': '0.7.6+commit.7338295f'})
    built = solc_compile(request, FIXTURE.parent, out / 'source', solc=solc)
    evm = built['contracts'][FIXTURE.name]['LegacyTypedCallGas']['evm']
    runtime, mapping = (evm['deployedBytecode'][key] for key in ('object', 'sourceMap'))
    sites = source_sites(built['sources'][FIXTURE.name]['ast'])
    selectors = evm['methodIdentifiers']
    cases = []
    for first in CHILDREN:
        for second in CHILDREN:
            for length in [0, 1, 31, 32, 33, 129]:
                for fail in [False, True]:
                    cases.append(('run(address,address,bytes,bytes,bool)',
                        ['address', 'address', 'bytes', 'bytes', 'bool'],
                        [address(first), address(second), bytes(range(length)), b'auxiliary', fail], 320000))
    for target in CHILDREN:
        for length in [0, 1, 32, 33, 129]:
            cases.append(('settle(address,uint256,uint256,bytes)',
                ['address', 'uint256', 'uint256', 'bytes'],
                [address(target), 17, 29, bytes(range(length))], 100000))
    transactions, expected, accounting_expected = [], [], []
    with Anvil(out / 'node') as node:
        sender = node.rpc('eth_accounts')[0]
        deployed = node.transact({'from': sender, 'data': '0x' + evm['bytecode']['object'], 'gas': hex(10000000)})
        if deployed['receipt']['status'] != '0x1':
            raise HarnessError('typed callback fixture deployment failed')
        caller = deployed['receipt']['contractAddress']
        if node.rpc('eth_getCode', caller, 'latest') != '0x' + runtime:
            raise HarnessError('source runtime differs from compiler output')
        node.rpc('anvil_setBalance', caller, hex(BALANCE))
        for child, code in zip(CHILDREN, CODES):
            node.rpc('anvil_setCode', address(child), '0x' + code)
            if node.rpc('eth_getCode', address(child), 'latest') != '0x' + code:
                raise HarnessError('independent gas child runtime differs')
        for i, (signature, types, values, budget) in enumerate(cases):
            selector = selectors[signature]
            payload = encode(types, values)
            record = node.transact({'from': sender, 'to': caller, 'data': '0x' + selector + payload.hex(),
                                    'gas': hex(budget)})
            receipt = record['receipt']
            trace = node.rpc('debug_traceTransaction', receipt['transactionHash'],
                {'enableMemory': True, 'disableStack': False, 'disableStorage': True})
            write_json(out / 'node' / (receipt['transactionHash'] + '.gas.json'), trace)
            block = node.rpc('eth_getBlockByHash', receipt['blockHash'], False)
            meter, left, accounting = evidence(trace, record['call'], record['prestate'], runtime,
                mapping, sites, coinbase=int(block['miner'], 16))
            transactions.append({'id': str(i), 'function': signature.split('(')[0],
                'args': [str(int.from_bytes(payload[n:n + 32], 'big')) for n in range(0, len(payload), 32)],
                'selector': str(int(selector, 16)), 'sender': str(int(sender, 16)),
                'target': str(int(caller, 16)), 'value': '0', 'timestamp': str(int(block['timestamp'], 16)),
                'blockNumber': str(int(receipt['blockNumber'], 16)), 'observe': [[str(int(caller, 16)), '0']],
                'observeAccounts': [str(child) for child in CHILDREN], 'sourceGas': meter})
            row = node.observe(record, str(i))
            def account(a, code=False):
                result = {'address': a, 'nonce': int(node.rpc('eth_getTransactionCount', a, 'latest'), 16),
                          'balance': int(node.rpc('eth_getBalance', a, 'latest'), 16)}
                if code:
                    result['code'] = node.rpc('eth_getCode', a, 'latest')
                return result
            expected.append({**{k: row[k] for k in ['id', 'status', 'data', 'events']},
                'serial': int(node.rpc('eth_getStorageAt', caller, '0x0', 'latest'), 16),
                'sourceGasLeft': left, 'deployment': {'creator': account(caller),
                    'accounts': [account(address(child), True) for child in CHILDREN]}})
            accounting_expected.append({'id': str(i), 'events': accounting})
        initial = {'account': str(int(caller, 16)), 'storage': [['0', '0']], 'accountNonce': '1',
            'initialBalances': [[str(int(caller, 16)), str(BALANCE)]],
            'accountCode': [[str(child), '0x' + code] for child, code in zip(CHILDREN, CODES)],
            'gasChildren': CHILDREN, 'transactions': transactions}
        write_json(out / 'node-provenance.json', node.provenance)
    write_json(out / 'input.json', initial)
    write_json(out / 'expected.json', expected)
    write_json(out / 'accounting-expected.json', accounting_expected)
    rows = replay(out / 'control', initial, args.optimized)
    if len(rows) != len(expected):
        raise HarnessError('model omitted callback transactions')
    for actual, want in zip(rows, expected):
        for key in ['id', 'status', 'data', 'events', 'sourceGasLeft', 'deployment']:
            if actual[key] != want[key]:
                raise HarnessError(f'{want["id"]}: {key}: {actual[key]} != {want[key]}')
        slots = [int(v, 16) for a, s, v in actual['storage'] if int(a, 16) == int(caller, 16) and int(s, 16) == 0]
        if slots != [want['serial']]:
            raise HarnessError('caller storage/rollback differs')
    rejected = check_rejections(out, initial, args.optimized)
    write_json(out / 'complete.json', {'cases': len(rows), 'evidenceRejections': rejected,
        'solc': release, 'optimized': args.optimized, 'fixtureSha256': hashlib.sha256(source.encode()).hexdigest(),
        'head': command(['git', 'rev-parse', 'HEAD']).strip(),
        'workingTreeClean': not command(['git', 'status', '--porcelain']).strip(),
        'scope': 'original-bytecode/Denote callback gas; fixed child programs; trusted EVM span meter'})
    print(f'{len(rows)} typed callback gas cases and {rejected} malformed-evidence controls passed')


if __name__ == '__main__':
    main()
