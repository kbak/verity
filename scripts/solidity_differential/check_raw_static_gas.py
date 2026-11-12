"""Original-bytecode gas for raw STATICCALL, memory allocation and word decoding."""
import argparse
import copy
import hashlib
import json
from pathlib import Path

from eth_abi import encode
from .anvil import Anvil
from .engine import HarnessError, command, solc_compile, source_compiler, write_json
from .check_legacy_static_words import FIXTURE, MODEL
from .check_static_call_gas import child_code
from .check_typed_callback_gas import address, replay
from .source_gas_trace import evidence, source_sites

PROGRAMS = [(0, 32, 'return'), ((1 << 256)-1, 32, 'return'), (42, 33, 'return'),
            (42, 64, 'return'), (42, 65, 'return'), (42, 0, 'return'),
            (42, 1, 'return'), (42, 31, 'return'), (42, 32, 'revert'),
            (42, 65, 'revert'), (0, 0, 'exceptional'), (0, 0, 'write'), (0, 32, 'gas')]
EMPTY = 0x3456


def reject_controls(out, initial, optimized, model):
    controls = {'missing': 'original bytecode gas evidence missing',
        'site': 'source gas observation site differs',
        'missing-read': 'missing or reordered source gas observation',
        'missing-call': 'missing or reordered source call gas boundary',
        'kind': 'source call request differs', 'value': 'source call request differs',
        'target': 'source call request differs', 'gas': 'source call request differs',
        'allowance': 'source child allowance differs from EIP-150 accounting',
        'gasLeft': 'child returned gas above its allowance',
        'success': 'source child outcome differs from functional execution',
        'returndata': 'source child outcome differs from functional execution',
        'extra': 'unconsumed source gas evidence'}
    for name, diagnostic in controls.items():
        bad = copy.deepcopy(initial)
        bad['transactions'] = bad['transactions'][:1]
        tx = bad['transactions'][0]
        events = tx['sourceGas']['events']
        index = next(i for i, e in enumerate(events) if e['type'] == 'call')
        call = events[index]
        if name == 'missing':
            del tx['sourceGas']
        elif name == 'site':
            events[index-1]['site'] = 'wrong-site'
        elif name == 'missing-read':
            events.pop(index-1)
        elif name == 'missing-call':
            events.pop(index)
        elif name == 'kind':
            call['kind'] = 'call'
        elif name == 'gasLeft':
            call[name] = call['allowance'] + 1
        elif name == 'success':
            call[name] = not call[name]
        elif name == 'returndata':
            call[name].append(0)
        elif name == 'extra':
            events.append({'type': 'end', 'cost': 0})
        else:
            call[name] += 1
        folder = out / ('reject-' + name)
        try:
            replay(folder, bad, optimized, model=model)
        except HarnessError:
            log = (folder / 'model.log').read_text()
            if ': error: ' + diagnostic not in log:
                raise HarnessError('wrong rejection: ' + name + '\n' + log)
        else:
            raise HarnessError('malformed evidence admitted: ' + name)
    write_json(out / 'rejections.json', controls)
    return len(controls)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--skip-build', action='store_true')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    if not args.skip_build:
        command(['turbo-lean', '--json', 'build', 'Contracts.SolidityImportSmoke.LegacyStaticWordModel'],
                log=out / 'build.log', timeout=1800)
    model = out / 'GasModel.lean'
    model.write_text(MODEL.read_text().replace('bytecodeHash := "none"',
                                            'bytecodeHash := "none", sourceGas := true'))
    source = FIXTURE.read_text()
    release, solc = source_compiler({'solc': '0.7.6+commit.7338295f'})
    built = solc_compile({'language': 'Solidity', 'sources': {FIXTURE.name: {'content': source}},
        'settings': {'evmVersion': 'istanbul', 'optimizer': {'enabled': args.optimized, 'runs': 200},
            'metadata': {'bytecodeHash': 'none'}, 'outputSelection': {'*': {'*': ['evm.bytecode.object',
            'evm.deployedBytecode.object', 'evm.deployedBytecode.sourceMap', 'evm.methodIdentifiers'],
            '': ['ast']}}}}, FIXTURE.parent, out / 'source', solc=solc)
    evm = built['contracts'][FIXTURE.name][FIXTURE.stem]['evm']
    runtime, mapping = (evm['deployedBytecode'][key] for key in ('object', 'sourceMap'))
    sites = source_sites(built['sources'][FIXTURE.name]['ast'])
    selectors = evm['methodIdentifiers']
    children, codes = [], {}
    for index, (word, length, mode) in enumerate(PROGRAMS):
        target = 0x2300 + index
        children.append({'address': target, 'word': word, 'length': length,
                         'mode': 'exceptional' if mode == 'write' else mode})
        codes[target] = child_code(word, length, mode)
    codes[EMPTY] = ''
    txs, expected, accounting_expected = [], [], []
    with Anvil(out / 'node') as node:
        sender = node.rpc('eth_accounts')[0]
        deployed = node.transact({'from': sender, 'data': '0x' + evm['bytecode']['object'],
                                 'gas': hex(10000000)})
        if deployed['receipt']['status'] != '0x1':
            raise HarnessError('raw static fixture deployment failed')
        caller = deployed['receipt']['contractAddress']
        if node.rpc('eth_getCode', caller, 'latest') != '0x' + runtime:
            raise HarnessError('original raw static runtime differs')
        for target, code in codes.items():
            node.rpc('anvil_setCode', address(target), '0x' + code)
            if node.rpc('eth_getCode', address(target), 'latest') != '0x' + code:
                raise HarnessError('raw static child runtime differs')

        def execute(signature, values):
            payload = encode(signature[signature.index('(')+1:-1].split(','), values)
            original = node.transact({'from': sender, 'to': caller,
                'data': '0x' + selectors[signature] + payload.hex(), 'gas': hex(180000)})
            ident = str(len(txs))
            receipt = original['receipt']
            trace = node.rpc('debug_traceTransaction', receipt['transactionHash'],
                {'enableMemory': True, 'disableStack': False, 'disableStorage': True})
            write_json(out / 'node' / (receipt['transactionHash'] + '.gas.json'), trace)
            block = node.rpc('eth_getBlockByHash', receipt['blockHash'], False)
            meter, left, accounting = evidence(trace, original['call'], original['prestate'],
                runtime, mapping, sites, coinbase=int(block['miner'], 16))
            observe = [[str(int(caller, 16)), '0'], [str(0x230b), '0']]
            txs.append({'id': ident, 'function': signature.split('(')[0],
                'args': [str(int.from_bytes(payload[n:n+32], 'big')) for n in range(0, len(payload), 32)],
                'selector': str(int(selectors[signature], 16)), 'sender': str(int(sender, 16)),
                'target': str(int(caller, 16)), 'value': '0', 'timestamp': str(int(block['timestamp'], 16)),
                'blockNumber': str(int(block['number'], 16)), 'observe': observe,
                'observeAccounts': [], 'sourceGas': meter})
            row = node.observe(original, ident, [(address(int(a)), '0x' + int(s).to_bytes(32, 'big').hex())
                                               for a, s in observe])
            expected.append({**{k: row[k] for k in ['id', 'status', 'data', 'events', 'storage']},
                             'sourceGasLeft': left})
            accounting_expected.append({'id': ident, 'events': accounting})

        for target in codes:
            for method in ['word', 'decoded', 'inspect']:
                execute(method + '(address,address)', [address(target), caller])
            execute('selfWord(address)', [address(target)])
            execute('twice(address,address,address)', [address(target), address(target), caller])
            execute('inspectPair(address,address,address)', [address(0x2301), address(target), caller])
            for minimum in [0, 1, (1 << 256)-1]:
                execute('atLeast(address,address,uint256)', [address(target), caller, minimum])
        write_json(out / 'node-provenance.json', node.provenance)
    initial = {'account': str(int(caller, 16)), 'storage': [], 'accountNonce': '1',
        'accountCode': [[str(target), '0x' + code] for target, code in codes.items()],
        'staticGasChildren': children, 'byteCallEnvironment': {'program': 'hash-static-oracle-v1',
            'accounts': [], 'emptyAccounts': [str(EMPTY)], 'gas': '1', 'recoveries': []}, 'transactions': txs}
    write_json(out / 'input.json', initial)
    write_json(out / 'expected.json', expected)
    write_json(out / 'accounting-expected.json', accounting_expected)
    rows = replay(out / 'control', initial, args.optimized, model=model)
    if len(rows) != len(expected):
        raise HarnessError('raw static model omitted transactions')
    rows = [{key: sorted(row[key]) if key == 'storage' else row[key] for key in want}
            for row, want in zip(rows, expected, strict=True)]
    if rows != expected:
        write_json(out / 'mismatches.json', [{'actual': a, 'expected': b}
            for a, b in zip(rows, expected) if a != b])
        raise HarnessError('raw static model differs from original EVM')
    warm = [e['context']['targetWarm'] for tx in txs for e in tx['sourceGas']['events'] if e['type'] == 'call']
    if set(warm) != {False, True}:
        raise HarnessError('campaign lacks cold or repeated warm static calls')
    controls = reject_controls(out, initial, args.optimized, model)
    write_json(out / 'complete.json', {'cases': len(txs), 'rejectionControls': controls,
        'optimized': args.optimized, 'sourceCompiler': release,
        'fixtureSha256': hashlib.sha256(source.encode()).hexdigest(),
        'head': command(['git', 'rev-parse', 'HEAD']).strip(),
        'workingTreeClean': not command(['git', 'status', '--porcelain']).strip(),
        'scope': 'original-bytecode gas and functional model; no generated gas equivalence'})
    print(f'{len(txs)} raw static gas cases and {controls} rejection controls passed')


if __name__ == '__main__':
    main()
