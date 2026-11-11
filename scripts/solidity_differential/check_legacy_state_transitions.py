"""Legacy writes/modifiers/events: exact source/model/generated state sequences.

Self-sender frames are explicit local impersonation, not reachable signed wallet
transactions. The independent oracle checks storage, ordered logs and revert data;
three-route agreement alone is insufficient. Gas and full-world frames are excluded.
"""
import argparse
import hashlib
from pathlib import Path
import random
import sys

from eth_abi import encode
from eth_utils import keccak

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes
from .check_interface_word_static_call import address, roots, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyStateTransitions.sol')
DRIVER = FIXTURE.with_name('LegacyStateTransitionsModel.lean')
MASK = (1 << 256) - 1
FUNCTIONS = {'links': ('setLimit(uint256)', 'insert(address,uint256)'),
             'scalar': ('set(uint8)', 'increment()', 'compound(uint8)', 'failAfterWrite(uint8)'),
             'stateless': ('record(uint256)',)}
CONTRACTS = {'links': 'LegacyStateTransitions', 'scalar': 'LegacyScalarEffects',
             'stateless': 'LegacyStatelessEffects'}


def word(value):
    return '0x' + value.to_bytes(32, 'big').hex()


def event(account, signature, types, values, *, indexed=False):
    if indexed:
        return {'address': account, 'topics': ['0x' + keccak(text=signature).hex(),
                '0x' + encode(types, values).hex()], 'data': '0x'}
    return {'address': account, 'topics': ['0x' + keccak(text=signature).hex()],
            'data': '0x' + encode(types, values).hex()}


def error(reason):
    return '0x' + (keccak(text='Error(string)')[:4] + encode(['string'], [reason])).hex()


def cases(kind, caller, count, random_cases, seed):
    outsider, self = SENDER, caller
    if kind == 'links':
        yield 'unauthorized-threshold', 0, [1], outsider
        yield 'unauthorized-insert', 1, [20, 1], outsider
        for n in (1, 3, 3, 0, 4, MASK):
            yield f'limit-{n}', 0, [n], self
        if count == MASK:
            yield 'persist-wrapped-count', 1, [30, MASK], self
        for key in (0, 1, int(caller, 16), 11):
            yield f'invalid-key-{key}', 1, [key, 2], self
        yield 'rollback-zero', 1, [20, 0], self
        yield 'rollback-bound', 1, [20, MASK], self
        yield 'insert-same-limit', 1, [20, min(count, 3) or 1], self
        yield 'insert-change-limit', 1, [21, 1], self
        yield 'duplicate', 1, [20, 1], self
        yield 'dirty-address-abi', 1, [(1 << 200) + 29, 1], self
        rng = random.Random(seed)
        for i in range(random_cases):
            yield f'random-{i}', 1, [rng.randrange(20, 28), rng.choice([0, 1, 2, 7, MASK])], self
    elif kind == 'scalar':
        yield 'unauthorized-write', 0, [17], outsider
        yield 'wrap-increment', 1, [], self
        yield 'set-max', 0, [255], self
        yield 'compound-and-post-modifier', 2, [255], self
        yield 'rollback-event', 3, [17], self
        yield 'permitted-zero', 3, [0], self
        yield 'abi-dirty-scalar', 0, [MASK], self
        yield 'compound-wrap', 2, [1], self
    else:
        yield 'unauthorized-event', 0, [MASK], outsider
        yield 'permitted-event', 0, [MASK], self
        yield 'permitted-zero', 0, [0], self


def scenario(kind, caller, layout, *, initial_count=3, random_cases=8, seed=7611,
             functions=None, fields=None, errors=None, events=None, dirty_mappings=False):
    """Requirement-level transition oracle; never reads either execution result."""
    functions = functions or FUNCTIONS[kind]
    fields = fields or ('links', 'count', 'limit')
    errors = errors or dict(context='context', bound='bound', zero='zero', key='key', duplicate='duplicate')
    events = events or ('Inserted(address)', 'Limit(uint256)')
    slots = {f['label']: int(f['slot']) for f in layout['storage']}
    calls = list(cases(kind, caller, initial_count, random_cases, seed))
    # SequenceRunner deliberately rejects value transfers before model execution.
    # This campaign supplies zero-value call frames; payable admission is tested separately.
    calls[:0] = [("truncated-head", 0, calls[0][2][:-1], caller)]
    initial = {int(f['slot']): 0 for f in layout['storage']}
    initial[9999] = 0xABCDE  # Unrelated canary, observed even if never touched.
    for name, slot in slots.items():
        if name.startswith('pad'):
            initial[slot] = 0xC001 + slot
    def mapping(key):
        return int.from_bytes(keccak(encode(['uint256', 'uint256'], [key, slots[fields[0]]])), 'big')
    if kind == 'links':
        keys = {0, 1, 11, 12, 13, int(caller, 16)} | {args[0] % (1 << 160) for _, i, args, _ in calls if i == 1}
        initial.update({mapping(key): 0 for key in keys})
        initial.update({mapping(k): v for k, v in ((1, 11), (11, 12), (12, 13), (13, 1))})
        if dirty_mappings:
            for key in keys:
                initial[mapping(key)] |= 0xABCDE << 160
        initial[slots[fields[1]]] = initial_count
        initial[slots[fields[2]]] = 2
    elif kind == 'scalar':
        initial[slots['stored']] = 0xABCDEF00 + 255
    initial_rows = [(caller, word(slot), word(value)) for slot, value in sorted(initial.items())]
    current, transactions, expected = dict(initial), [], {}
    for label, index, args, sender in calls:
        signature = functions[index]
        # Deliberately encode raw words, including noncanonical ABI-v1 scalars.
        data = keccak(text=signature)[:4] + b''.join(n.to_bytes(32, 'big') for n in args)
        ident = str(len(transactions))
        tx = {'id': ident, 'label': label, 'function': signature.split('(')[0], 'args': args,
              'sender': sender, 'target': caller, 'value': '0x0', 'data': '0x' + data.hex(),
              'timestamp': 1000000100 + len(transactions), 'blockNumber': 2 + len(transactions)}
        transactions.append(tx)
        next_state, logs, reason = dict(current), [], None
        if label == "truncated-head":
            reason = ""  # Dispatcher failure, before any source guard or write.
        elif sender != caller:
            reason = errors['context']
        elif kind == 'links':
            n = args[-1]
            if index == 1:
                key = args[0] % (1 << 160)
                if key in (0, 1, int(caller, 16)):
                    reason = errors['key']
                elif current[mapping(key)] & ((1 << 160) - 1) != 0:
                    reason = errors['duplicate']
                else:
                    address_mask = (1 << 160) - 1
                    next_state[mapping(key)] = ((current[mapping(key)] & (MASK ^ address_mask)) |
                                                (current[mapping(1)] & address_mask))
                    next_state[mapping(1)] = (current[mapping(1)] & (MASK ^ address_mask)) | key
                    next_state[slots[fields[1]]] = (current[slots[fields[1]]] + 1) & MASK
                    logs.append(event(caller, events[0], ['address'], ['0x' + key.to_bytes(20, 'big').hex()], indexed=True))
            if reason is None and (index == 0 or n != current[slots[fields[2]]]):
                if n > next_state[slots[fields[1]]]:
                    reason = errors['bound']
                elif n == 0:
                    reason = errors['zero']
                else:
                    next_state[slots[fields[2]]] = n
                    logs.append(event(caller, events[1], ['uint256'], [n]))
        elif kind == 'scalar':
            slot = slots['stored']
            n = args[0] % 256 if args else 0
            low = ((current[slot] + (n if index == 2 else 1)) % 256
                   if index in (1, 2) else n)
            next_state[slot] = (current[slot] & (MASK ^ 255)) | low
            logs.append(event(caller, 'Value(uint8)', ['uint8'], [low]))
            if index == 2:
                next_state[slot] = (current[slot] & (MASK ^ 255)) | ((low + 1) % 256)
            if index == 3 and n:
                reason = 'rollback'
        else:
            logs.append(event(caller, 'Value(uint256)', ['uint256'], args))
        if reason is None:
            current = next_state
        expected[ident] = {'status': 'revert' if reason is not None else 'ok',
                          'data': error(reason) if reason else '0x',
                          'events': [] if reason is not None else logs,
                          'storage': [[caller, word(slot), word(value)] for slot, value in sorted(current.items())]}
    return initial_rows, transactions, expected


def campaign(output, *, kind='links', context=0, optimized=False, initial_count=3,
             fixture=FIXTURE, contract=None, functions=None, extra_sources=None,
             fields=None, errors=None, events=None, dirty_mappings=False, prepared=False,
             scenario_builder=scenario, import_functions=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    # Parallel execution must share fixed artifacts: build once before workers.
    # ImplementationIdentity still rejects every source/artifact change.
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.Differential', 'Compiler.SolidityImport.SequenceRunner',
                 '--project-dir', '.'], timeout=1800, log=output / 'build.log')
    contract = contract or CONTRACTS[kind]
    functions = functions or FUNCTIONS[kind]
    source = fixture.read_text()
    # Pad declaration count without changing any method's source.
    brace = source.index('{', source.index('contract ' + contract + ' '))
    source = source[:brace+1] + ''.join(f'\nuint256 private pad{i};' for i in range(context)) + source[brace+1:]
    sources = {'Sequence.sol': {'content': source},
               **{name: {'content': text} for name, text in (extra_sources or {}).items()}}
    for name, item in sources.items():
        path = output / name
        if not path.resolve().is_relative_to(output):
            raise HarnessError('source escapes output directory')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(item['content'])
    template = DRIVER.read_text().replace('from "Contracts/SolidityImportSmoke" entry "LegacyStateTransitions.sol"',
                                        f'from "{output}" entry "Sequence.sol"')
    template = template.replace('  contract LegacyStateTransitions', '  contract ' + contract)
    template = template.replace('  function setLimit(uint256)\n  function insert(address,uint256)',
                                '\n'.join('  function ' + f.replace('address[]', '«address[]»') for f in (import_functions or functions)))
    if optimized:
        template = template.replace('optimizerRuns := none', 'optimizerRuns := some 200')
    driver = output / 'Driver.lean'
    driver.write_text(template)
    original = solc_compile({'language': 'Solidity', 'sources': sources, 'settings': {
        'evmVersion': 'istanbul', 'optimizer': {'enabled': optimized, 'runs': 200},
        'metadata': {'bytecodeHash': 'none'}, 'outputSelection': {'*': {'*': [
            'evm.bytecode.object', 'evm.methodIdentifiers', 'storageLayout']}}}},
        output, output / 'source-solc', solc=Path.cwd() / '.lake/solidity-import/solc-0.7.6')['contracts']['Sequence.sol'][contract]
    # Import selection uses source enum names; selectors use their canonical ABI types.
    selected = [f.replace('«', '').replace('»', '') for f in roots(template)]
    if selected != list(import_functions or functions):
        raise HarnessError('driver roots differ from the requested source signatures')
    if [f.split('(')[0] for f in selected] != [f.split('(')[0] for f in functions]:
        raise HarnessError('import roots and canonical function selectors differ')
    write_json(output / 'selectors.json', [int(original['evm']['methodIdentifiers'][f.replace('«', '').replace('»', '')], 16)
                                           for f in functions])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', output / 'selectors.json', output / 'model.yul'],
            timeout=900, log=output / 'compile.log')
    generated = solc_compile({'language': 'Yul', 'sources': {'Model.yul': {'content': (output / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, output, output / 'model-solc', solc=SOLC)['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('expected one generated model')
    caller = address(0)
    initial, calls, expected = scenario_builder(kind, caller, original['storageLayout'], initial_count=initial_count,
        functions=functions, fields=fields, errors=errors, events=events, dirty_mappings=dirty_mappings)
    write_json(output / 'initial-storage.json', initial)
    write_json(output / 'transactions.json', calls)
    write_json(output / 'expectations.json', expected)
    adapters = {
        'source': EVM(output / 'A', ['0x' + original['evm']['bytecode']['object']], initial, impersonated_senders=[caller]),
        'model': Denote(output / 'B', driver, caller, initial),
        'compiled': EVM(output / 'C', ['0x' + next(iter(generated.values()))['evm']['bytecode']['object']], initial, impersonated_senders=[caller])}
    watched = {(account, slot) for account, slot, _ in initial}
    def observing(adapter):
        return lambda txs, plan: adapter(txs, [sorted(set(map(tuple, slots)) | watched) for slots in plan])
    result = replay_three_routes(calls, {name: observing(adapter) for name, adapter in adapters.items()})
    mismatches = []
    for route, rows in result['observations'].items():
        for tx, row in zip(calls, rows, strict=True):
            wanted = expected[tx['id']]
            for key in ('status', 'data', 'events', 'storage'):
                actual = row[key]
                if key == 'storage':
                    actual = sorted(entry for entry in actual if tuple(entry[:2]) in watched)
                if actual != wanted[key]:
                    mismatches.append({'route': route, 'id': tx['id'], 'label': tx['label'], 'field': key,
                                       'expected': wanted[key], 'actual': actual})
    report = {**result, 'expectationMismatches': mismatches, 'count': len(calls),
              'kind': kind, 'context': context, 'optimized': optimized, 'initialCount': initial_count,
              'dirtyMappings': dirty_mappings,
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
              'scope': 'finite zero-value call-frame sequences, explicit initial storage and self-sender impersonation; gas/value transfers excluded'}
    write_json(output / 'results.json', report)
    passed = not result['divergences'] and not mismatches
    write_json(output / 'summary.json', {k: v for k, v in report.items() if k not in ('observations', 'discovery', 'slots')} | {'passed': passed})
    print(f'{kind}: {len(calls)} cases, {len(result["divergences"])} divergences, {len(mismatches)} expectation failures', flush=True)
    return int(not passed)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--kind', choices=CONTRACTS, default='links')
    parser.add_argument('--context', type=int, default=0)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--prepared', action='store_true',
                        help='reuse artifacts explicitly built for this exact source before parallel runs')
    parser.add_argument('--dirty-mappings', action='store_true')
    parser.add_argument('--initial-count', type=int, default=3)
    args = parser.parse_args()
    try:
        return campaign(args.output, kind=args.kind, context=args.context, optimized=args.optimized,
                        initial_count=args.initial_count, dirty_mappings=args.dirty_mappings, prepared=args.prepared)
    except (HarnessError, ValueError, KeyError, OSError) as exc:
        print(f'HARNESS ERROR: {exc}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
