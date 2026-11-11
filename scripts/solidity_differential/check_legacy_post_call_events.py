"""Exact ordered caller/child logs, nested rollback, and independent account expectations."""
import argparse
import random
from pathlib import Path
from eth_abi import encode
from eth_utils import keccak
from .check_legacy_raw_calls import campaign, GAS, FUNDS, MASK, SENDER, EMPTY

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyPostCallEvents.sol')
DRIVER = FIXTURE.with_name('LegacyPostCallEventsModel.lean')
ORACLE = FIXTURE.with_name('PostCallLogOracle.sol')


def event(owner, topics, data):
    return {'address': owner, 'topics': ['0x' + int(t).to_bytes(32, 'big').hex() for t in topics],
            'data': '0x' + data.hex()}


def transactions(seed, caller, accounts, random_cases):
    rng = random.Random(seed)
    balances = {caller: FUNDS, accounts[0]: 5, accounts[1]: 17, EMPTY: 0, SENDER: 1 << 200}
    nonces = {caller: 1, accounts[0]: 1, accounts[1]: 1, EMPTY: 0, SENDER: 3}
    storage, calls, expected, logs = {}, [], {}, []
    starting = int.from_bytes(keccak(text='Starting(address,uint256)'), 'big')
    outcome = int.from_bytes(keccak(text='Outcome(address,bool,uint256)'), 'big')

    def child(target, owner, sender, value, data):
        nonlocal storage, logs
        if target == EMPTY:
            return True, b''
        assert target in accounts
        saved_storage, saved_logs = dict(storage), list(logs)
        storage[(owner, 7)] = (storage.get((owner, 7), 0) + 1) & MASK
        o, s = int(owner, 16), int(sender, 16)
        logs.extend(event(owner, topics, data) for topics in
                    [[], [o], [s, value], [0x33, o, s], [0x44, o, s, value]])
        mode = data[0] if data else 0
        if mode in (1, 2):
            storage, logs = saved_storage, saved_logs
            return False, data if mode == 1 else b''
        if mode in (3, 4, 5):
            assert len(data) >= 21
            nested = '0x' + data[1:21].hex()
            delegated = mode == 4
            success, _ = child(nested, owner if delegated else nested,
                               sender if delegated else owner, value if delegated else 0, data[21:])
            logs.append(event(owner, [0x55, int(success)], data))
            if mode == 5:
                storage, logs = saved_storage, saved_logs
                return False, data
        return True, data

    def invoke(target, amount, data, operation, incoming):
        nonlocal balances
        saved = dict(balances)
        if operation == 0:
            if amount > balances[caller]:
                return False, b''
            balances[caller] -= amount
            balances[target] += amount
        ok, returned = child(target, caller if operation else target,
                              SENDER if operation else caller, incoming if operation else amount, data)
        if not ok:
            balances = saved
        return ok, returned

    def add(target, next_target, amount, data, operation, mode, incoming, *, late=False, truncated=False):
        nonlocal balances, storage, logs
        signature = 'lateInvalid(address,bytes,uint8,uint256)' if late else \
            'run(address,address,uint256,bytes,uint8,uint256,uint256)'
        values = [target, data, operation, GAS] if late else \
            [target, next_target, amount, data, operation, GAS, mode]
        types = signature[signature.index('(')+1:-1].replace('uint8', 'uint256').split(',')
        payload = encode(types, values)
        if truncated:
            payload = payload[:17]
        padded = payload + bytes((-len(payload)) % 32)
        ident = str(len(calls))
        calls.append({'id': ident, 'function': 'lateInvalid' if late else 'run',
            'args': [int.from_bytes(padded[i:i+32], 'big') for i in range(0, len(padded), 32)],
            'sender': SENDER, 'target': caller, 'value': hex(incoming),
            'data': '0x' + keccak(text=signature)[:4].hex() + payload.hex(),
            'timestamp': 1000000100 + len(calls), 'blockNumber': 4 + len(calls)})
        saved_balances, saved_storage = dict(balances), dict(storage)
        nonces[SENDER] += 1
        balances[SENDER] -= incoming
        balances[caller] += incoming
        status, returned, logs = 'ok', b'', []
        operation %= 256
        if truncated:
            status = 'revert'
        else:
            storage[(caller, 0)] = (storage.get((caller, 0), 0) + 1) & MASK
            logs.append(event(caller, [starting, int(SENDER, 16)], encode(['uint256'], [storage[(caller, 0)]])))
            if not late and operation >= 2:
                status = 'invalid'
            else:
                ok, child_return = invoke(target, 0 if late else amount, data, 0 if late else operation, incoming)
                logs.append(event(caller, [outcome, int(target, 16)],
                                  encode(['bool', 'uint256'], [ok, 0 if late else len(child_return)])))
                if late:
                    if operation >= 2:
                        status = 'invalid'
                    else:
                        returned = encode(['uint256'], [operation])
                else:
                    if mode == 1:
                        ok, child_return = invoke(next_target, amount, data, operation, incoming)
                        logs.append(event(caller, [outcome, int(next_target, 16)],
                                          encode(['bool', 'uint256'], [ok, len(child_return)])))
                    if mode == 2:
                        status, returned = 'revert', keccak(text='Error(string)')[:4] + encode(['string'], ['LATE'])
                    elif mode == 3:
                        status, returned = 'revert', child_return
                    else:
                        returned = encode(['bool', 'uint256'], [ok, len(child_return)])
        if status != 'ok':
            balances, storage, logs = saved_balances, saved_storage, []
        expected[ident] = {'status': status, 'data': '0x' + returned.hex(), 'events': list(logs),
            'balances': dict(balances), 'nonces': dict(nonces),
            'storage': [[owner, slot, word] for (owner, slot), word in storage.items()]}

    payloads = [b'']
    for size in (1, 2, 31, 32, 33, 65, 129):
        for mode in (0, 1, 2):
            payloads.append(bytes([mode]) + rng.randbytes(size - 1))
    def nested(mode, target, data):
        return bytes([mode]) + bytes.fromhex(target[2:]) + data
    for mode in (3, 4, 5):
        for inner in (b'\0child\0', b'\1revert\0', b'\2invalid\0'):
            payloads.append(nested(mode, accounts[1], inner))
        payloads.append(nested(mode, EMPTY, b'\0'))
        payloads.append(nested(mode, accounts[1], nested(4, accounts[0], b'\0deep\0')))
    for operation in (0, 1):
        for data in payloads:
            for mode in (0, 1, 2, 3):
                add(accounts[0], accounts[1], 1, data, operation, mode, 7)
    for operation in (0, 1, 2, 255, 256, 257, 258, MASK):
        add(accounts[0], accounts[1], 0, b'\0', operation, 0, 3, late=True)
        add(accounts[0], accounts[1], 0, b'\0', operation, 0, 3)
    for target in (accounts[0], EMPTY):
        for operation in (0, 1):
            for mode in (0, 1, 2, 3):
                for amount in (0, balances[caller] + 11, MASK):
                    add(target, accounts[1], amount, b'\0funds\0', operation, mode, 11)
    for _ in range(random_cases):
        add(rng.choice([*accounts, EMPTY]), accounts[1], rng.randrange(5), rng.choice(payloads),
            rng.randrange(2), rng.randrange(4), rng.randrange(50))
    add(accounts[0], accounts[1], 0, b'', 0, 0, 3, truncated=True)
    return calls, expected


def run(output, optimized=False, fixture=FIXTURE, driver_template=DRIVER, extra_sources=None):
    return campaign(output, optimized=optimized, fixture=fixture, driver_template=driver_template,
        extra_sources=extra_sources, value_transactions=True, make_transactions=transactions,
        oracle_fixture=ORACLE, mock_module='PostCallLogMocks', mock_program='post-call-logs-v1')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--optimized', action='store_true')
    return run(**vars(parser.parse_args()))


if __name__ == '__main__':
    raise SystemExit(main())
