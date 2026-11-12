"""Original-bytecode gas for legacy recovery, bytes4 validation and bool STATICCALL."""
import argparse
import copy
import hashlib
import json
import random
from pathlib import Path

from eth_abi import encode
from eth_keys import keys
from eth_keys.constants import SECPK1_N

from .anvil import Anvil
from .engine import HarnessError, command, solc_compile, source_compiler, write_json
from .check_legacy_signature_calls import BACKEND, recovery
from .check_typed_callback_gas import address, replay as replay_model
from .source_gas_trace import evidence, source_sites

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyStaticCallGas.sol')
MODEL = FIXTURE.with_name('LegacyStaticCallGasModel.lean')
MAGIC = 0x1626ba7e << 224
# Every configured child has an independently modeled, verified runtime.
PROGRAMS = [(MAGIC, 32, 'return'), (MAGIC + 1, 32, 'return'), (0, 32, 'return'),
            (MAGIC, 31, 'return'), ((1 << 256) - 1, 65, 'return'), (MAGIC, 0, 'return'),
            ((1 << 256) - 1, 33, 'revert'), (0, 0, 'revert'), (0, 0, 'exceptional'),
            (0, 0, 'write'), (0, 32, 'gas')]
EMPTY = 0x3456


def replay(out, payload, optimized):
    return replay_model(out, payload, optimized, model=MODEL)


def child_code(word, length, mode):
    if mode == 'exceptional':
        return 'fe'
    if mode == 'write':
        return '600160005500'  # SSTORE is exceptional in a static frame.
    prefix = '5a' if mode == 'gas' else '7f' + word.to_bytes(32, 'big').hex()
    return prefix + '60005260' + bytes([length]).hex() + '6000' + ('fd' if mode == 'revert' else 'f3')


def vectors():
    rng = random.Random(4801)
    rows, cases = {}, []
    for _ in range(2):
        key = keys.PrivateKey(rng.randrange(1, SECPK1_N).to_bytes(32, 'big'), backend=BACKEND)
        h = rng.randbytes(32)
        signature = key.sign_msg_hash(h)
        v, r, s = signature.v + 27, signature.r, signature.s
        for actual_v, actual_r, actual_s in [(v, r, s), (55-v, r, SECPK1_N-s),
                (v+256, r, s), (0, r, s), (v, 0, s), (v, r, 0), (v, r, SECPK1_N)]:
            words = (int.from_bytes(h, 'big'), actual_v % 256, actual_r, actual_s)
            rows[words] = recovery(h, actual_v % 256, actual_r, actual_s)
            rows[(words[0], 0, actual_r, actual_s)] = []
            cases.append([h, actual_v, actual_r.to_bytes(32, 'big'), actual_s.to_bytes(32, 'big')])
    return cases, [{'args': list(map(str, args)), 'output': list(map(str, output))}
                   for args, output in sorted(rows.items())]


def check_rejections(out, initial, optimized):
    diagnostics = {
        'missing': 'original bytecode gas evidence missing',
        'site': 'source gas observation site differs',
        'missing-read': 'missing or reordered source gas observation',
        'swapped-read-call': 'missing or reordered source gas observation',
        'missing-call': 'missing or reordered source call gas boundary',
        'kind': 'source call request differs',
        'value': 'source call request differs',
        'target': 'source call request differs',
        'operand': 'source call request differs',
        'allowance': 'source child allowance differs from EIP-150 accounting',
        'value-charge': 'source call value-charge mode differs',
        'returned-gas': 'child returned gas above its allowance',
        'recovery-cost': 'source recovery gas differs from precompile cost',
        'recovery-outcome': 'source recovery gas differs from precompile cost',
        'returndata': 'source child outcome differs from functional execution',
        'truncated': 'unconsumed source gas evidence',
        'extra': 'unconsumed source gas evidence',
    }
    results = {}
    for name, diagnostic in diagnostics.items():
        bad = copy.deepcopy(initial)
        bad['transactions'] = bad['transactions'][:1]
        tx = bad['transactions'][0]
        events = tx['sourceGas']['events']
        index = next(i for i, e in enumerate(events) if e['type'] == 'call')
        event = events[index]
        if event['target'] != 1 or events[index-1]['type'] != 'read':
            raise HarnessError('recovery control lacks its actual GAS/STATICCALL')
        if name == 'missing':
            del tx['sourceGas']
        elif name == 'site':
            events[index-1]['site'] = 'wrong-site'
        elif name == 'missing-read':
            events.pop(index-1)
        elif name == 'swapped-read-call':
            events[index-1], events[index] = events[index], events[index-1]
        elif name == 'missing-call':
            events.pop(index)
        elif name == 'kind':
            event['kind'] = 'call'
        elif name == 'value-charge':
            event['context']['transfersValue'] = True
        elif name == 'returned-gas':
            event['gasLeft'] = event['allowance'] + 1
        elif name == 'recovery-cost':
            event['gasLeft'] -= 1
        elif name == 'recovery-outcome':
            event['success'] = False
        elif name == 'returndata':
            event['returndata'].append(0)
        elif name == 'truncated':
            events.pop()
        elif name == 'extra':
            events.append({'type': 'end', 'cost': 0})
        else:
            event[{'operand': 'gas'}.get(name, name)] += 1
        folder = out / ('reject-' + name)
        try:
            replay(folder, bad, optimized)
        except HarnessError:
            log = (folder / 'model.log').read_text()
            if ': error: ' + diagnostic not in log:
                raise HarnessError('wrong rejection or instrumentation failure: ' + name + '\n' + log)
        else:
            raise HarnessError('malformed static evidence accepted: ' + name)
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
        command(['turbo-lean', '--json', 'build', 'Contracts.SolidityImportSmoke.LegacyStaticCallGasModel'],
                log=out / 'build.log', timeout=1800)
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
    signatures, recoveries = vectors()
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
        deployment = node.transact({'from': sender, 'data': '0x' + evm['bytecode']['object'],
                                   'gas': hex(10000000)})
        if deployment['receipt']['status'] != '0x1':
            raise HarnessError('static fixture deployment failed')
        caller = deployment['receipt']['contractAddress']
        if node.rpc('eth_getCode', caller, 'latest') != '0x' + runtime:
            raise HarnessError('original static runtime differs')
        for target, code in codes.items():
            node.rpc('anvil_setCode', address(target), '0x' + code)
            if node.rpc('eth_getCode', address(target), 'latest') != '0x' + code:
                raise HarnessError('static child runtime differs')

        def execute(signature, values, budget=180000, record=True):
            types = signature[signature.index('(')+1:-1].split(',')
            payload = encode(types, values)
            original = node.transact({'from': sender, 'to': caller,
                'data': '0x' + selectors[signature] + payload.hex(), 'gas': hex(budget)})
            if not record:
                return original
            ident = str(len(txs))
            receipt = original['receipt']
            trace = node.rpc('debug_traceTransaction', receipt['transactionHash'],
                {'enableMemory': True, 'disableStack': False, 'disableStorage': True})
            write_json(out / 'node' / (receipt['transactionHash'] + '.gas.json'), trace)
            block = node.rpc('eth_getBlockByHash', receipt['blockHash'], False)
            meter, left, accounting = evidence(trace, original['call'], original['prestate'],
                runtime, mapping, sites, coinbase=int(block['miner'], 16))
            observe = [[str(int(caller, 16)), '0'], [str(0x2309), '0']]
            txs.append({'id': ident, 'function': signature.split('(')[0],
                'args': [str(int.from_bytes(payload[n:n+32], 'big')) for n in range(0, len(payload), 32)],
                'selector': str(int(selectors[signature], 16)), 'sender': str(int(sender, 16)),
                'target': str(int(caller, 16)), 'value': '0', 'timestamp': str(int(block['timestamp'], 16)),
                'blockNumber': str(int(block['number'], 16)), 'observe': observe,
                'observeAccounts': [], 'sourceGas': meter})
            row = node.observe(original, ident, [(address(int(a)), '0x' + int(s).to_bytes(32, 'big').hex()) for a, s in observe])
            expected.append({**{k: row[k] for k in ['id', 'status', 'data', 'events', 'storage']},
                             'sourceGasLeft': left})
            accounting_expected.append({'id': ident, 'events': accounting})
            return original

        for values in signatures:
            for method in ['recover', 'repeated', 'boundary']:
                execute(method + '(bytes32,uint256,bytes32,bytes32)', values)
        for target in codes:
            for size in [0, 1, 31, 32, 33, 65]:
                for method in ['word', 'checked']:
                    execute(method + '(address,bytes32,bytes)',
                            [address(target), signatures[0][0], bytes(range(size))])
            execute('predicate(address,uint256)', [address(target), 17])
            for enabled in [False, True]:
                execute('gated(bool,address,uint256)', [enabled, address(target), 29])
        # Locate adjacent transaction budgets giving the precompile 2999 and 3000 gas.
        boundary = 'boundary(bytes32,uint256,bytes32,bytes32)'
        threshold_values = next(values for values in signatures if values[1] % 256 == 0)
        payload = bytes.fromhex(selectors[boundary]) + encode(
            ['bytes32', 'uint256', 'bytes32', 'bytes32'], threshold_values)
        low = 21000 + sum(4 if b == 0 else 16 for b in payload)
        high = low + 12000
        while low + 1 < high:
            middle = (low + high) // 2
            probe = execute(boundary, threshold_values, middle, record=False)
            calls = probe['call'].get('calls', [])
            allowance = int(calls[0]['gas'], 16) if calls else 0
            if allowance < 3000:
                low = middle
            else:
                high = middle
        boundary_rows = []
        for budget in [low, high, high + 1]:
            # Isolate the real child boundary: solc may exhaust its parent afterwards.
            # Root OOG is deliberately not admitted into the complete-frame replay.
            original = execute(boundary, threshold_values, budget, record=False)
            child = original['call']['calls'][0]
            allowance = int(child['gas'], 16)
            success, used = 'error' not in child, int(child['gasUsed'], 16)
            if success != (allowance >= 3000) or used != min(allowance, 3000):
                raise HarnessError('original recovery precompile cost/threshold differs')
            boundary_rows.append({'budget': budget, 'allowance': allowance,
                'success': success, 'gasUsed': used, 'parentFrameModeled': False,
                'parentError': original['call'].get('error')})
        if [r['allowance'] for r in boundary_rows] != [2999, 3000, 3001]:
            raise HarnessError('missing exact precompile gas threshold')
        write_json(out / 'precompile-boundary.json', boundary_rows)
        write_json(out / 'node-provenance.json', node.provenance)
    initial = {'account': str(int(caller, 16)), 'storage': [], 'accountNonce': '1',
        'accountCode': [[str(target), '0x' + code] for target, code in codes.items()],
        'staticGasChildren': children, 'byteCallEnvironment': {'program': 'hash-static-oracle-v1',
            'accounts': [], 'emptyAccounts': [], 'gas': '1', 'recoveries': recoveries}, 'transactions': txs}
    write_json(out / 'input.json', initial)
    write_json(out / 'expected.json', expected)
    write_json(out / 'accounting-expected.json', accounting_expected)
    rows = replay(out / 'control', initial, args.optimized)
    if len(rows) != len(expected):
        raise HarnessError('static model omitted transactions')
    for actual, want in zip(rows, expected, strict=True):
        for key, value in want.items():
            got = sorted(actual[key]) if key == 'storage' else actual[key]
            value = sorted(value) if key == 'storage' else value
            if got != value:
                raise HarnessError(f'{want["id"]}: {key}: {actual[key]} != {value}')
    rejected = check_rejections(out, initial, args.optimized)
    write_json(out / 'complete.json', {'cases': len(rows), 'evidenceRejections': rejected,
        'isolatedPrecompileBoundaries': len(boundary_rows),
        'solc': release, 'optimized': args.optimized, 'fixtureSha256': hashlib.sha256(source.encode()).hexdigest(),
        'head': command(['git', 'rev-parse', 'HEAD']).strip(),
        'workingTreeClean': not command(['git', 'status', '--porcelain']).strip(),
        'scope': 'original-bytecode/Denote static gas; independent recovery and fixed child programs'})
    print(f'{len(rows)} static gas cases and {rejected} malformed-evidence controls passed')


if __name__ == '__main__':
    main()
