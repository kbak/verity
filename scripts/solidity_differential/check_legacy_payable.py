"""Payable named entries with explicit zero-fee EOA envelopes and independent expectations."""
import argparse
import random
from pathlib import Path
from eth_abi import encode
from eth_utils import keccak
from .check_legacy_raw_calls import campaign, GAS, FUNDS, MASK, SENDER, EMPTY

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyPayable.sol')
DRIVER = FIXTURE.with_name('LegacyPayableModel.lean')


def transactions(seed, caller, accounts, random_cases, *, stateless=False):
    rng = random.Random(seed)
    balances = {caller: FUNDS, accounts[0]: 5, accounts[1]: 17, EMPTY: 0, SENDER: 1 << 200}
    nonces = {caller: 1, accounts[0]: 1, accounts[1]: 1, EMPTY: 0, SENDER: 3}
    storage, calls, expected = {}, [], {}

    def add(method, values, incoming, truncated=False):
        nonlocal balances, storage
        types = ('address,uint256,bytes,uint8,uint256' if method in ('run', 'forward') else
                 'uint8' if method == 'enumUse' else 'uint256')
        payload = encode(types.replace('uint8', 'uint256').split(','), values)
        if truncated:
            payload = payload[:17]
        signature = method + '(' + types + ')'
        padded = payload + bytes((-len(payload)) % 32)
        ident = str(len(calls))
        calls.append({'id': ident, 'function': method,
            'args': [int.from_bytes(padded[i:i+32], 'big') for i in range(0, len(padded), 32)],
            'sender': SENDER, 'target': caller, 'value': hex(incoming),
            'data': '0x' + keccak(text=signature)[:4].hex() + payload.hex(),
            'timestamp': 1000000100 + len(calls), 'blockNumber': 4 + len(calls)})
        before_balances, before_storage = dict(balances), dict(storage)
        assert incoming <= balances[SENDER]
        nonces[SENDER] += 1
        balances[SENDER] -= incoming
        balances[caller] += incoming
        status, output, events = 'ok', b'', []
        if truncated or (method == 'nonpayable' and incoming):
            status = 'revert'
        elif method == 'accept':
            output = encode(['uint256'] * 3, [incoming, balances[caller], values[0]])
        elif method in ('deposit', 'guarded', 'reject'):
            if method != 'reject':
                storage[(caller, 0)] = (storage.get((caller, 0), 0) + incoming) & MASK
                events = [{'address': caller, 'topics': ['0x' + keccak(text='Paid(address,uint256,uint256)').hex(),
                          '0x' + int(SENDER, 16).to_bytes(32, 'big').hex()],
                          'data': '0x' + encode(['uint256', 'uint256'], [incoming, values[0]]).hex()}]
            if method != 'deposit' and values[0] == 0:
                status, output = 'revert', keccak(text='Error(string)')[:4] + encode(['string'], ['PAY'])
            elif method == 'deposit':
                output = encode(['uint256'] * 4,
                    [incoming, balances[caller], storage[(caller, 0)], incoming])
        elif method == 'nonpayable':
            if not stateless:
                storage[(caller, 0)] = (storage.get((caller, 0), 0) + values[0]) & MASK
            output = encode(['uint256'], [values[0] if stateless else storage[(caller, 0)]])
        elif method == 'enumUse':
            operation = values[0] % 256
            if operation >= 2:
                status = 'invalid'
            else:
                output = encode(['uint256'], [operation])
        else:
            target, amount, data, operation, gas = values
            operation %= 256
            if operation >= 2:
                status = 'invalid'
            else:
                returned, success = b'', False
                if operation == 1 or amount <= balances[caller]:
                    child_before = dict(balances)
                    if operation == 0:
                        balances[caller] -= amount
                        balances[target] += amount
                    if target == EMPTY:
                        success = True
                    elif data and data[0] in (1, 2):
                        balances = child_before
                        returned = data if data[0] == 1 else b''
                    else:
                        owner = caller if operation == 1 else target
                        words = [int.from_bytes(keccak(data), 'big'),
                            int(SENDER if operation else caller, 16), int(owner, 16),
                            incoming if operation else amount, balances[owner], int(SENDER, 16),
                            (storage.get((owner, 6), 0) + 1) & MASK]
                        storage.update({(owner, slot): word for slot, word in enumerate(words)})
                        success, returned = True, data
                if method == 'forward':
                    status, output = 'revert', returned
                else:
                    output = encode(['bool', 'uint256'], [success, len(returned)])
        if status != 'ok':
            balances, storage, events = before_balances, before_storage, []
        expected[ident] = {'status': status, 'data': '0x' + output.hex(),
            'balances': dict(balances), 'nonces': dict(nonces), 'events': events,
            'storage': [[owner, slot, value] for (owner, slot), value in storage.items()]}

    for value in (0, 1, 7, 1 << 128):
        for tag in (0, 1, MASK):
            add('accept' if stateless else 'deposit', [tag], value)
            add('reject' if stateless else 'guarded', [tag], value)
            add('nonpayable', [tag], value)
            add('accept' if stateless else 'deposit', [tag], value, truncated=True)
    if not stateless:
        for value in (0, 11):
            for operation in (0, 1, 2, 255, 256, 257, 258, MASK):
                add('enumUse', [operation], value)
        for operation in (0, 1, 2, 256, 257):
            for length in (0, 1, 31, 32, 33, 65, 129):
                for mode in ((0,) if length == 0 else (0, 1, 2)):
                    data = bytes([mode]) + rng.randbytes(length - 1) if length else b''
                    for method in ('run', 'forward'):
                        incoming = 13
                        amount = balances[caller] + incoming
                        add(method, [accounts[0], amount, data, operation, GAS], incoming)
        for target in (accounts[0], EMPTY):
            for operation in (0, 1):
                for method in ('run', 'forward'):
                    add(method, [target, MASK, b'\x00overspend\x00', operation, GAS], 17)
    for _ in range(random_cases):
        value, tag = rng.randrange(1000), rng.choice([0, 1, MASK])
        add(rng.choice(['accept', 'reject', 'nonpayable'] if stateless else
            ['deposit', 'guarded', 'nonpayable']), [tag], value)
    return calls, expected


def run(output, optimized=False, stateless=False):
    output = Path(output).resolve()
    driver, contract = DRIVER, 'LegacyPayable'
    if stateless:
        output.parent.mkdir(parents=True, exist_ok=True)
        driver = output.parent / (output.name + '-stateless.lean')
        source = DRIVER.read_text()
        start, end = source.index('  function deposit('), source.index('/-- Imported')
        source = source[:start] + ('  function accept(uint256)\n  function reject(uint256)\n'
                                 '  function nonpayable(uint256)\n') + source[end:]
        driver.write_text(source.replace('  contract LegacyPayable', '  contract LegacyPayableStateless'))
        contract = 'LegacyPayableStateless'
    return campaign(output, optimized=optimized, fixture=FIXTURE, driver_template=driver,
        contract_name=contract, value_transactions=True,
        make_transactions=lambda *args: transactions(*args, stateless=stateless))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--stateless', action='store_true')
    return run(**vars(parser.parse_args()))


if __name__ == '__main__':
    raise SystemExit(main())
