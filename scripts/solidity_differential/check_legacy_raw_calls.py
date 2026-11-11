"""Legacy raw calls: source EVM / Denote / compiled EVM with explicit child code.

Checks complete return/revert bytes, balances, storage and execution context.
Gas/call-depth equivalence and arbitrary external programs are not proved.
"""
import argparse
import copy
import hashlib
from pathlib import Path
import random
import sys

from eth_abi import encode
from eth_utils import keccak

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .deployment import observe_accounts, compare_deployment_sequences
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes
from .check_interface_word_static_call import address, roots, SENDER, EMPTY

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyRawCalls.sol')
DRIVER = FIXTURE.with_name('LegacyRawCallsModel.lean')
ORACLE = FIXTURE.with_name('RawCallOracle.sol')
MASK = (1 << 256) - 1
GAS = 1000000
FUNDS = 1000000


def transactions(seed, caller, accounts, random_cases, *, methods=('run', 'forward', 'twice', 'compare')):
    rng = random.Random(seed)
    calls, expected = [], {}
    balances = {caller: FUNDS, accounts[0]: 5, accounts[1]: 17, EMPTY: 0}
    storage = {}
    signature = '(address,uint256,bytes,uint8,uint256)'

    def add(method, values, targets, amount, data, operation):
        nonlocal balances, storage
        args = ('(address,address,uint256,bytes,uint8,uint256)' if method == 'twice'
                else '(uint8,uint8)' if method == 'compare' else
                '(uint8)' if method in ('ignore', 'castHelper') else signature)
        sig = method + args
        types = args[1:-1].replace('uint8', 'uint256').split(',')
        payload = encode(types, values)
        ident = str(len(calls))
        calls.append({'id': ident, 'function': method, 'args': [int.from_bytes(payload[i:i+32], 'big')
                      for i in range(0, len(payload), 32)], 'sender': SENDER, 'target': caller,
                      'value': '0x0', 'data': '0x' + keccak(text=sig)[:4].hex() + payload.hex(),
                      'timestamp': 1000000100 + len(calls), 'blockNumber': 4 + len(calls)})
        old_balances, old_storage = dict(balances), dict(storage)
        operation %= 256
        if method in ('ignore', 'castHelper'):
            status, output = ('ok', encode(['uint256'], [7])) if method == 'ignore' else (
                ('invalid', b'') if operation >= 2 else ('ok', encode(['uint256'], [operation])))
        elif method == 'compare':
            a, b = (v % 256 for v in values)
            status, output = ('invalid', b'') if max(a, b) >= 2 else ('ok', encode(
                ['bool'] * 6, [a == b, a != b, a < b, a <= b, a > b, a >= b]))
        elif operation >= 2:
            status, output = 'invalid', b''
        else:
            success, returned = False, b''
            for target in targets:
                success, returned = False, b''
                if operation == 0 and amount > balances[caller]:
                    continue
                before = dict(balances)
                if operation == 0:
                    balances[caller] -= amount
                    balances[target] += amount
                if target == EMPTY:
                    success = True
                    continue
                mode = data[0] if data else 0
                if mode in (1, 2):
                    balances = before
                    returned = data if mode == 1 else b''
                    continue
                owner = caller if operation == 1 else target
                values_at = [int.from_bytes(keccak(data), 'big'),
                             int(SENDER if operation == 1 else caller, 16), int(owner, 16),
                             0 if operation == 1 else amount, balances[owner], int(SENDER, 16),
                             (storage.get((owner, 6), 0) + 1) & MASK]
                storage.update({(owner, slot): value for slot, value in enumerate(values_at)})
                success, returned = True, data
            if method == 'forward':
                balances, storage = old_balances, old_storage
                status, output = 'revert', returned
            else:
                status, output = 'ok', encode(['bool', 'uint256'], [success, len(returned)])
        expected[ident] = {'status': status, 'data': '0x' + output.hex(),
                           'balances': dict(balances),
                           'storage': [[owner, slot, value] for (owner, slot), value in storage.items()]}

    for operation in (0, 1):
        for length in (0, 1, 31, 32, 33, 65, 129, 257):
            for mode in ((0,) if length == 0 else (0, 1, 2)):
                data = (bytes([mode]) + rng.randbytes(length - 1)) if length else b''
                for target in (accounts[0], EMPTY):
                    for amount in (0, 7, MASK):
                        for method in ('run', 'forward'):
                            if method in methods:
                                add(method, [target, amount, data, operation, GAS],
                                    [target], amount, data, operation)
    if 'twice' in methods:
        for first in (accounts[0], EMPTY):
            for second in (accounts[1], EMPTY):
                for operation in (0, 1):
                    for mode in (0, 1, 2):
                        data = bytes([mode]) + rng.randbytes(64)
                        for amount in (7, FUNDS // 2 + 1, FUNDS, MASK):
                            add('twice', [first, second, amount, data, operation, GAS],
                                [first, second], amount, data, operation)
    if 'compare' in methods:
        for a in (0, 1, 2, 255, 256, 257, 258, MASK):
            for b in (0, 1, 2, 255, 256, 257):
                add('compare', [a, b], [], 0, b'', a)
    for operation in (0, 1, 2, 255, 256, 257, 258, MASK):
        for method in ('ignore', 'castHelper'):
            add(method, [operation], [], 0, b'', operation)
    for operation in (2, 255, 256, 257, 258, MASK):
        for method in ('run', 'forward'):
            if method in methods:
                data = b'\x00enum-boundary\x00'
                add(method, [accounts[0], 3, data, operation, GAS], [accounts[0]], 3, data, operation)
    for _ in range(random_cases):
        operation = rng.choice([0, 1, 2, 256, 257])
        target = rng.choice([*accounts, EMPTY])
        length = rng.randrange(0, 512)
        data = bytes([rng.randrange(3)]) + rng.randbytes(length) if length else b''
        amount = rng.randrange(0, 1000)
        method = 'run'
        add(method, [target, amount, data, operation, GAS], [target], amount, data, operation)
    return calls, expected


def campaign(directory, *, optimized=False, seed=7401, random_cases=24,
             fixture=FIXTURE, driver_template=DRIVER, extra_sources=None,
             make_transactions=transactions):
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
             'Compiler.SolidityImport.Differential', 'Compiler.SolidityImport.SequenceRunner',
             'Compiler.SolidityImport.RawCallMocks', '--project-dir', '.'], timeout=1800,
            log=directory / 'build.log')
    source = fixture.read_text()
    (directory / 'Sequence.sol').write_text(source)
    for name, text in (extra_sources or {}).items():
        path = directory / name
        if Path(name).is_absolute() or not path.resolve().is_relative_to(directory):
            raise HarnessError('extra source must stay within the campaign directory')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    template = driver_template.read_text()
    anchor = f'from "Contracts/SolidityImportSmoke" entry "{fixture.name}"'
    if template.count(anchor) != 1:
        raise HarnessError('one import anchor required')
    template = template.replace(anchor, f'from "{directory}" entry "Sequence.sol"')
    if optimized:
        template = template.replace('optimizerRuns := none', 'optimizerRuns := some 200')
    driver = directory / 'Driver.lean'
    driver.write_text(template)
    source_contract = solc_compile({'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source},
                    **{name: {'content': text} for name, text in (extra_sources or {}).items()}},
        'settings': {'evmVersion': 'istanbul', 'optimizer': {'enabled': optimized, 'runs': 200},
            'metadata': {'bytecodeHash': 'none'}, 'outputSelection': {'*': {'*': [
                'evm.bytecode.object', 'evm.methodIdentifiers']}}}}, directory,
        directory / 'source-solc', solc=Path.cwd() / '.lake/solidity-import/solc-0.7.6'
        )['contracts']['Sequence.sol'][fixture.stem]
    identifiers = source_contract['evm']['methodIdentifiers']
    write_json(directory / 'selectors.json', [int(identifiers[s.replace("Enum.Operation", "uint8").replace("Operation", "uint8")], 16)
        for s in roots(template)])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log')
    model = solc_compile({'language': 'Yul',
        'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, directory,
        directory / 'model-solc', solc=SOLC)['contracts']['Model.yul']
    if len(model) != 1:
        raise HarnessError('expected one compiled model object')
    mock = solc_compile({'language': 'Solidity',
        'sources': {ORACLE.name: {'content': ORACLE.read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.deployedBytecode.object']}}}},
        directory, directory / 'oracle-solc', solc=SOLC)['contracts'][ORACLE.name]['RawCallOracle']['evm']
    caller, accounts = address(0), [address(1), address(2)]
    balances = [(caller, FUNDS), (accounts[0], 5), (accounts[1], 17), (EMPTY, 0)]
    deployments = ['0x' + mock['bytecode']['object']] * 2
    calls, expected = make_transactions(seed, caller, accounts, random_cases)
    write_json(directory / 'transactions.json', calls)
    write_json(directory / 'expectations.json', expected)
    environment = {'program': 'raw-context-echo-v1', 'accounts': [str(int(a, 16)) for a in accounts],
                   'emptyAccounts': [str(int(EMPTY, 16))]}
    plan = sorted([*accounts, EMPTY])
    deployment_rows = {}

    def observe(route):
        def observe_one(node, record, ident, slots):
            row = node.observe(record, ident, slots)
            deployment_rows.setdefault(route, {})[ident] = observe_accounts(node, record, caller, plan)
            return row
        return observe_one

    denote = Denote(directory / 'B', driver, caller, byte_call_environment=environment,
        account_code=[(a, '0x' + mock['deployedBytecode']['object']) for a in accounts],
        account_nonce=1, account_nonces=[(a, 1) for a in accounts], initial_balances=balances,
        timeout=1800)

    def model_adapter(txs, slots):
        copied = copy.deepcopy(txs)
        for tx in copied:
            tx['observeAccounts'] = plan
        rows = denote(copied, slots)
        deployment_rows['model'] = {row['id']: row.pop('deployment') for row in rows}
        return rows

    adapters = {
        'source': EVM(directory / 'A', ['0x' + source_contract['evm']['bytecode']['object'],
            *deployments], observer=observe('source'), initial_balances=balances),
        'model': model_adapter,
        'compiled': EVM(directory / 'C', ['0x' + next(iter(model.values()))['evm']['bytecode']['object'],
            *deployments], observer=observe('compiled'), initial_balances=balances)}
    result = replay_three_routes(calls, adapters)
    observations = {route: [{**row, 'deployment': deployment_rows[route][row['id']]} for row in rows]
                    for route, rows in result['observations'].items()}
    divergences = compare_deployment_sequences([tx['id'] for tx in calls], observations,
                                               [plan for _ in calls])
    mismatches = []
    for route, rows in observations.items():
        for row in rows:
            exp = expected[row['id']]
            observed_balances = {a['address']: a['balance'] for a in
                                 [row['deployment']['creator'], *row['deployment']['accounts']]}
            seen = {(a, int(slot, 16)): int(value, 16) for a, slot, value in row['storage']}
            # Every expected persistent write must be observed; other touched slots stay zero.
            wanted = {(a, slot): value for a, slot, value in exp['storage']}
            correct_storage = all(seen.get(k) == v for k, v in wanted.items()) and all(
                wanted.get(k, 0) == v for k, v in seen.items())
            if row['status'] != exp['status'] or row['data'] != exp['data'] or not correct_storage or \
                    observed_balances != exp['balances']:
                mismatches.append({'route': route, 'id': row['id'], 'actual': row,
                                   'expected': exp})
    report = {**result, 'observations': observations, 'divergences': divergences,
              'count': len(calls), 'cases': len(calls), 'optimized': optimized, 'seed': seed,
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
              'expectationMismatches': mismatches}
    write_json(directory / 'results.json', report)
    if divergences or mismatches:
        return 1
    write_json(directory / 'summary.json', {'passed': True, 'count': len(calls),
        'scope': 'finite byte/storage/balance/context A/B/C; fixed external program; gas excluded'})
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--seed', type=int, default=7401)
    parser.add_argument('--random-cases', type=int, default=24)
    args = parser.parse_args()
    if args.random_cases < 0:
        parser.error('--random-cases must be nonnegative')
    return campaign(args.output, optimized=args.optimized, seed=args.seed, random_cases=args.random_cases)


if __name__ == '__main__':
    sys.exit(main())
