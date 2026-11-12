"""Void callbacks: independent ABI, ordering, context, balances and rollback checks."""
import argparse
import random
from pathlib import Path
from eth_abi import encode
from eth_utils import keccak
from .check_legacy_raw_calls import campaign, FUNDS, MASK, SENDER, EMPTY
from .check_legacy_post_call_events import event

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyVoidCallbacks.sol')
DRIVER = FIXTURE.with_name('LegacyVoidCallbacksModel.lean')
ORACLE = FIXTURE.with_name('VoidCallOracle.sol')
BEFORE = 'beforeCall(address,uint256,bytes,uint8,uint256,uint256,uint256,address,address,bytes,address)'
AFTER = 'afterCall(bytes32,bool)'


def encoded(signature, values, *, dirty_enum=False):
    types = signature[signature.index('(')+1:-1].split(',') if values else []
    if dirty_enum:
        types = ['uint256' if t == 'uint8' else t for t in types]
    return keccak(text=signature)[:4] + encode(types, values)


def transactions(seed, caller, accounts, random_cases, *, guard_slot=1, seeded_guard=None,
                 before_signature=BEFORE, after_signature=AFTER, run_lengths=(0, 33)):
    rng = random.Random(seed)
    balances = {caller: FUNDS, accounts[0]: 5, accounts[1]: 17, EMPTY: 0, SENDER: 1 << 200}
    nonces = {caller: 1, accounts[0]: 1, accounts[1]: 1, EMPTY: 0, SENDER: 3}
    storage, calls, expected, logs = {}, [], {}, []
    if seeded_guard is not None:
        storage[(caller, guard_slot)] = int(seeded_guard, 16)
    before_id, after_id = (keccak(text=s)[:4] for s in (before_signature, after_signature))
    starting = int.from_bytes(keccak(text='Starting(address,uint256)'), 'big')
    outcome = int.from_bytes(keccak(text='Outcome(address,bool,uint256)'), 'big')

    def child(target, owner, sender, value, data):
        nonlocal storage, logs
        if target == EMPTY:
            return True, b''
        assert target in accounts
        before, after = data[:4] == before_id, data[:4] == after_id
        mode = int.from_bytes(data[132:164], 'big') if before else (
            storage.get((owner, 20), 0) if after else (data[0] if data else 0))
        if (before and mode == 200) or (after and mode == 202) or (not before and not after and mode == 1):
            return False, data
        if (before and mode == 201) or (after and mode == 203) or (not before and not after and mode == 2):
            return False, b''
        if before:
            storage[(owner, 20)] = mode
        values = [storage.get((owner, 21), 0) + 1, int.from_bytes(keccak(data), 'big'),
                  int(sender, 16), int(owner, 16), value]
        storage.update({(owner, 21+i): v & MASK for i, v in enumerate(values)})
        logs.append(event(owner, [], data))
        return True, (data + bytes(128))[:mode % 128] if before or after else data

    def add(signature, values, incoming=0, *, truncated=False):
        nonlocal balances, storage, logs
        data = encoded(signature, values, dirty_enum=True)
        if truncated:
            data = data[:21]
        payload = data[4:]
        padded = payload + bytes((-len(payload)) % 32)
        ident = str(len(calls))
        calls.append({'id': ident, 'function': signature.split('(')[0],
            'args': [int.from_bytes(padded[i:i+32], 'big') for i in range(0, len(padded), 32)],
            'sender': SENDER, 'target': caller, 'value': hex(incoming), 'data': '0x' + data.hex(),
            'timestamp': 1000000100 + len(calls), 'blockNumber': 4 + len(calls)})
        saved_balances, saved_storage = dict(balances), dict(storage)
        nonces[SENDER] += 1
        balances[SENDER] -= incoming
        balances[caller] += incoming
        status, returned, logs = 'ok', b'', []
        method = signature.split('(')[0]
        if truncated or (incoming and method != 'run'):
            status = 'revert'
        elif method == 'configure':
            storage[(caller, guard_slot)] = values[0]
        elif method == 'readCallback':
            returned = encode(['uint256'], [storage.get((caller, guard_slot), 0) % (1 << 160)])
        else:
            if method == 'run':
                target, amount, input_, operation, auxiliary, mode = values
                callback = '0x' + (storage.get((caller, guard_slot), 0) % (1 << 160)).to_bytes(20, 'big').hex()
                storage[(caller, 0)] = storage.get((caller, 0), 0) + 1
                token = storage[(caller, 0)].to_bytes(32, 'big')
                logs.append(event(caller, [starting, int(SENDER, 16)], encode(['uint256'], [storage[(caller, 0)]])))
            else:
                if method == 'aliasBuffers':
                    callback, input_, auxiliary, operation, shift, mode = values
                    size = len(input_) if shift == 0 else int.from_bytes(input_[shift-32:shift], 'big')
                    auxiliary = input_ if shift == 0 else input_[shift:shift+size]
                else:
                    callback, input_, auxiliary, operation, mode = values
                if method == 'headAlias':
                    input_ = bytes(7)
                if method == 'lengthAlias':
                    input_ = bytes(257)
                target, amount = callback, mode
            operation %= 256
            has_callback = method != 'run' or int(callback, 16) != 0
            if operation >= 2:
                status = 'invalid'
            elif has_callback:
                if callback == EMPTY or int(callback, 16) == 0:
                    status = 'revert'
                else:
                    request = encoded(before_signature, [target, amount, input_, operation, mode, 7, 8, "0x" + "00" * 20, "0x" + "00" * 20, auxiliary, SENDER])
                    if method == 'lengthAlias':
                        request = request[:356] + (1).to_bytes(32, 'big') + request[388:]
                    ok, returned = child(callback, callback, caller, 0, request)
                    if not ok:
                        status = 'revert'
            if status == 'ok' and method == 'run':
                old_balances = dict(balances)
                if operation == 0 and amount > balances[caller]:
                    success = False
                else:
                    if operation == 0:
                        balances[caller] -= amount
                        balances[target] += amount
                    success, _ = child(target, caller if operation else target,
                                       SENDER if operation else caller, incoming if operation else amount, input_)
                    if not success:
                        balances = old_balances
                logs.append(event(caller, [outcome, int(target, 16)], encode(['bool', 'uint256'], [success, 0])))
                if has_callback:
                    ok, returned = child(callback, callback, caller, 0, encoded(after_signature, [token, success]))
                    if not ok:
                        status = 'revert'
                if status == 'ok':
                    returned = encode(['bool'], [success])
            elif status == 'ok':
                returned = b''
        if status != 'ok':
            balances, storage, logs = saved_balances, saved_storage, []
        expected[ident] = {'status': status, 'data': '0x' + returned.hex(), 'events': list(logs),
            'balances': dict(balances), 'nonces': dict(nonces),
            'storage': [[owner, slot, word] for (owner, slot), word in storage.items()]}

    run = 'run(address,uint256,bytes,uint8,bytes,uint256)'
    notify = 'notify(address,bytes,bytes,uint8,uint256)'
    callback_words = (int(accounts[0], 16), int(accounts[0], 16) + (1 << 255), 0, 1 << 200, int(EMPTY, 16))
    if seeded_guard is not None:
        callback_words = (int(seeded_guard, 16),)
    for callback_word in callback_words:
        if seeded_guard is None:
            add('configure(uint256)', [callback_word])
        add('readCallback()', [])
        for mode in (0, 1, 31, 32, 33, 65, 200, 201, 202, 203):
            for operation in (0, 1):
                for length in run_lengths:
                    input_ = b'\x00' + rng.randbytes(length-1) if length else b''
                    add(run, [accounts[1], 7, input_, operation, rng.randbytes(length), mode], incoming=13)
    if seeded_guard is None:
        add('configure(uint256)', [int(accounts[0], 16)])
    for length in (0, 1, 31, 32, 33, 65, 129, 257):
        for mode in (0, 1, 32, 65, 200, 201):
            values = [accounts[0], rng.randbytes(length), rng.randbytes(length // 2), 1, mode]
            add(notify, values)
            add('mixed(address,bytes,bytes,uint8,uint256)', values)
    for mode in (0, 65, 200):
        for method in ('headAlias', 'lengthAlias'):
            add(method + '(address,bytes,bytes,uint8,uint256)', [accounts[0], b'ignored', b'aux', 0, mode])
    for size in (0, 1, 31, 32, 33, 65):
        input_ = size.to_bytes(32, 'big') + rng.randbytes(96)
        for shift in (0, 32):
            add('aliasBuffers(address,bytes,bytes,uint8,uint256,uint256)',
                [accounts[0], input_, b'unused', 0, shift, 65])
    for operation in (2, 255, 256, 257, 258, MASK):
        add(notify, [accounts[0], b'a', b'b', operation, 0])
        add(run, [accounts[1], 0, b'', operation, b'', 0])
    for mode in (1, 2):
        for callback_mode in (0, 202, 203):
            add(run, [accounts[1], 7, bytes([mode]) + b'failed', 0, b'aux', callback_mode], 19)
    add(run, [EMPTY, MASK, b'', 0, b'', 0], 7)
    add(run, [EMPTY, 7, b'', 0, b'', 0], 0)
    add(notify, [EMPTY, b'', b'', 0, 0])
    add(notify, [accounts[0], b'', b'', 0, 0], 1)
    add(run, [accounts[1], 0, b'', 0, b'', 0], 11, truncated=True)
    for _ in range(random_cases):
        add(run, [rng.choice([*accounts, EMPTY]), rng.randrange(30),
                  bytes([rng.randrange(3)]) + rng.randbytes(rng.randrange(128)), rng.randrange(2),
                  rng.randbytes(rng.randrange(128)), rng.choice([0, 31, 65, 200, 201, 202, 203])], rng.randrange(20))
    return calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--seed', type=int, default=7501)
    parser.add_argument('--random-cases', type=int, default=24)
    args = parser.parse_args()
    result = campaign(args.output, optimized=args.optimized, seed=args.seed, random_cases=args.random_cases,
        fixture=FIXTURE, driver_template=DRIVER, make_transactions=transactions, value_transactions=True,
        oracle_fixture=ORACLE, mock_module='VoidCallMocks', mock_program='void-callbacks-v1')
    return result


if __name__ == '__main__':
    raise SystemExit(main())
