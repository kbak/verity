"""Ordered signature authorization against three execution routes.

The independent oracle decodes raw records, recovers signers with eth-keys,
checks the seeded membership/approval world, and compares exact return bytes.
A source mutation keeps this oracle and the positive controls unchanged.
"""
import argparse
from pathlib import Path
import random
import sys

from eth_abi import encode
from eth_keys import keys
from eth_utils import keccak

from .check_legacy_signature_calls import (
    BACKEND, MAGIC, MASK, RESPONSES, SECPK1_N, SENDER, campaign, recovery,
)
from .check_legacy_byte_pointers import fail, ok

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyOrderedSignatures.sol')
DRIVER = FIXTURE.with_name('LegacyOrderedSignaturesModel.lean')
HASH = keccak(b'ordered signature authorization')
PAYLOAD = b'bound validator payload'
PREFIX = b'\x19Ethereum Signed Message:\n32'
ERRORS = {name: name for name in
          ('threshold', 'length', 'offset', 'header', 'payload', 'validator', 'approval', 'member')}
PRIVATE_KEYS = [keys.PrivateKey(i.to_bytes(32, 'big'), backend=BACKEND) for i in range(11, 17)]
MEMBERS = [int.from_bytes(k.public_key.to_canonical_address(), 'big') for k in PRIVATE_KEYS]


def validator_parameters(accounts):
    parameters = list(RESPONSES)
    calldata = keccak(text='isValidSignature(bytes32,bytes)')[:4] + encode(
        ['bytes32', 'bytes'], [HASH, PAYLOAD])
    parameters[3] = (MAGIC ^ int.from_bytes(keccak(calldata), 'big'), False, 32, MASK)
    return dict(zip((int(a, 16) for a in accounts), parameters, strict=True))


def member_set(accounts):
    # Seed invalid distinguished addresses too: their rejection must be due to
    # ordering/sentinel guards, not an accidentally empty membership mapping.
    return set(MEMBERS + [0, 1] + [int(a, 16) for a in accounts])


def initial_storage(caller, accounts, layout, *, threshold=3,
                    field_names=('members', 'threshold', 'approvals')):
    fields = {field['label']: int(field['slot']) for field in layout['storage']}
    member_slot, threshold_slot, approval_slot = (fields[name] for name in field_names)
    def slot(key, base):
        return int.from_bytes(keccak(encode(['uint256', 'uint256'], [key, base])), 'big')
    rows = [(caller, slot(member, member_slot), 2) for member in member_set(accounts)]
    rows.append((caller, threshold_slot, threshold))
    rows.extend((caller, slot(int.from_bytes(HASH, 'big'), slot(member, approval_slot)), 1)
                for member in MEMBERS)
    rows.extend((account, index, int(value))
                for account in accounts
                for index, value in enumerate(validator_parameters(accounts)[int(account, 16)]))
    return [(account, '0x' + key.to_bytes(32, 'big').hex(),
             '0x' + value.to_bytes(32, 'big').hex()) for account, key, value in rows]


def record(r, s, tag):
    return r.to_bytes(32, 'big') + s.to_bytes(32, 'big') + bytes([tag])


def signed(index, h=HASH, *, prefixed=False, high_s=False):
    signature = PRIVATE_KEYS[index].sign_msg_hash(keccak(PREFIX + h) if prefixed else h)
    v, r, s = signature.vrs
    if high_s:
        v, s = 1 - v, SECPK1_N - s
    return MEMBERS[index], record(r, s, v + (31 if prefixed else 27)), False


def approved(member, high_bits=0):
    return member, record(member | high_bits, 0, 1), False


def contract(member, payload=PAYLOAD):
    return member, payload, True


def bundle(items):
    items = sorted(items, key=lambda item: item[0])
    static, tail = b'', b''
    for member, data, is_contract in items:
        if not is_contract:
            static += data
        else:
            static += record(member, 65 * len(items) + len(tail), 0)
            tail += len(data).to_bytes(32, 'big') + data
    return static + tail


class AuthorizationOracle:
    """Independent record decoder, with explicit cryptographic/external oracles."""
    def __init__(self, accounts, errors=ERRORS, threshold=3):
        self.members = member_set(accounts)
        self.validators = validator_parameters(accounts)
        self.errors, self.threshold, self.recoveries = errors, threshold, {}

    def validator(self, target, h, data):
        if target not in self.validators:
            return 'revert', '0x'
        value, failed, length, mask = self.validators[target]
        calldata = keccak(text='isValidSignature(bytes32,bytes)')[:4] + encode(
            ['bytes32', 'bytes'], [h, data])
        raw = value ^ (int.from_bytes(keccak(calldata), 'big') & mask)
        memory = raw.to_bytes(32, 'big') + bytes(32) + (128).to_bytes(32, 'big') + bytes(32) + calldata
        if failed:
            return 'revert', '0x' + memory.ljust(length, b'\0')[:length].hex()
        if length < 32:
            return 'revert', '0x'
        return None if raw >> 224 == MAGIC >> 224 else fail(self.errors['validator'])

    def recover(self, h, tag, r, s):
        digest, v = (keccak(PREFIX + h), tag - 4) if tag > 30 else (h, tag)
        output = recovery(digest, v, r, s)
        self.recoveries[(int.from_bytes(digest, 'big'), v, r, s)] = output
        return output[0] if output else 0

    def evaluate(self, executor, h, data, count, *, threshold=False):
        def reject(name):
            return fail(self.errors[name])
        if threshold:
            count = self.threshold
            if count == 0:
                return reject('threshold')
        if count * 65 > MASK:
            return 'revert', '0x'
        if len(data) < count * 65:
            return reject('length')
        previous = 0
        for i in range(count):
            chunk = data[65*i:65*(i+1)]
            r, s, tag = int.from_bytes(chunk[:32], 'big'), int.from_bytes(chunk[32:64], 'big'), chunk[64]
            if tag == 0:
                current = r % (1 << 160)
                if s < count * 65:
                    return reject('offset')
                if s + 32 > MASK:
                    return 'revert', '0x'
                if s + 32 > len(data):
                    return reject('header')
                size = int.from_bytes(data[s:s+32], 'big')
                if s + 32 + size > MASK:
                    return 'revert', '0x'
                if s + 32 + size > len(data):
                    return reject('payload')
                failed = self.validator(current, h, data[s+32:s+32+size])
                if failed is not None:
                    return failed
            elif tag == 1:
                current = r % (1 << 160)
                if executor != current and not (current in MEMBERS and h == HASH):
                    return reject('approval')
            else:
                current = self.recover(h, tag, r, s)
            if current <= previous or current not in self.members or current == 1:
                return reject('member')
            previous = current
        return ok(1)


def transactions(seed, caller, accounts, random_cases, *, errors=ERRORS, threshold=3):
    rng = random.Random(seed)
    oracle = AuthorizationOracle(accounts, errors, threshold)
    calls, expectations = [], {}

    def add(label, data, count, executor=int(SENDER, 16), h=HASH, wrapper=False):
        signature = ('checkThreshold(address,bytes32,bytes)' if wrapper else
                     'checkN(address,bytes32,bytes,uint256)')
        values = ['0x' + executor.to_bytes(20, 'big').hex(), h, data] + ([] if wrapper else [count])
        raw = encode(['address', 'bytes32', 'bytes'] + ([] if wrapper else ['uint256']), values)
        ident = str(len(calls))
        calls.append({'id': ident, 'label': label, 'function': signature.split('(')[0],
            'args': [int.from_bytes(raw[i:i+32], 'big') for i in range(0, len(raw), 32)],
            'sender': SENDER, 'target': caller, 'value': '0x0',
            'data': '0x' + keccak(text=signature)[:4].hex() + raw.hex(),
            'timestamp': 1000000100 + len(calls), 'blockNumber': len(accounts) + 2 + len(calls)})
        # Include recovery requests past a rejected record too. A mutation may
        # reach them; a missing mock row must never masquerade as detection.
        for i in range(min(oracle.threshold if wrapper else count, len(data) // 65)):
            chunk = data[65*i:65*(i+1)]
            if chunk[64] > 1:
                oracle.recover(h, chunk[64], int.from_bytes(chunk[:32], 'big'),
                               int.from_bytes(chunk[32:64], 'big'))
        expectations[ident] = oracle.evaluate(executor, h, data, count, threshold=wrapper)

    add('zero-count', b'', 0)
    add('zero-count-ignores-tail', b'ignored', 0)
    for count in (1, 2, 3, 4, 6):
        for prefixed in (False, True):
            for high_s in (False, True):
                data = bundle([signed(i, prefixed=prefixed, high_s=high_s) for i in range(count)])
                add('distinct-recovered', data, count)
                add('truncated-static', data[:count*65-1], count)
                add('valid-prefix-ignores-extra', data + record(0, 0, 2), count)
                add('reversed-order', b''.join(reversed([data[i:i+65] for i in range(0,len(data),65)])), count)
                add('threshold', data, 0, wrapper=True)
    for i in range(6):
        member = MEMBERS[i]
        add('approved-storage', bundle([approved(member)]), 1)
        add('executor-is-signer', bundle([approved(member)]), 1, executor=member, h=bytes(32))
        add('missing-approval', bundle([approved(member)]), 1, h=bytes(32))
        add('approval-high-bits-cleaned', bundle([approved(member, MASK ^ ((1<<160)-1))]), 1)
        add('wrong-message', bundle([signed(i)]), 1, h=keccak(HASH))
        for a, b in ((signed(i), signed(i)), (signed(i), signed(i, prefixed=True)),
                     (signed(i), approved(member)), (approved(member), approved(member))):
            add('duplicate-signer', bundle([a, b]), 2)
        add('duplicate-signer', bundle([signed(i)] * 3), 0, wrapper=True)
        add('duplicate-signer', bundle([signed(i), signed(i, prefixed=True), approved(member)]),
            0, wrapper=True)
    outside = keys.PrivateKey((97).to_bytes(32, 'big'), backend=BACKEND).sign_msg_hash(HASH)
    v, r, s = outside.vrs
    add('unregistered-recovered', record(r, s, v + 27), 1)
    for member in (0, 1, 2, int(SENDER, 16)):
        add('zero-member-executor' if member == 0 else 'invalid-member-executor',
            bundle([approved(member)]), 1, executor=member)
    for target in accounts + [SENDER]:
        member = int(target, 16)
        for payload in (b'', b'x', PAYLOAD, PAYLOAD + b'!', bytes(32), bytes(33), bytes(64), bytes(65)):
            add('contract-payload', bundle([contract(member, payload)]), 1)
        add('contract-duplicate', bundle([contract(member), contract(member)]), 2)
        add('contract-duplicate', bundle([contract(member)] * 3), 0, wrapper=True)
    for offset in (0, 64, 65, 66, 96, 97, MASK-31, MASK):
        for size in (0, 1, 32, MASK):
            data = record(int(accounts[0], 16), offset, 0) + size.to_bytes(32, 'big') + b'x'
            add('contract-offset-boundary', data, 1)
    for tag in (2, 26, 27, 28, 29, 30, 31, 32, 33, 255):
        for r, s in ((0, 0), (1, 1), (SECPK1_N, 1), (1, SECPK1_N)):
            add('recovery-boundary', record(r, s, tag), 1)
    mixed = [signed(0), signed(1, prefixed=True), approved(MEMBERS[2]), contract(int(accounts[3],16))]
    add('all-four-modes', bundle(mixed), 4)
    add('threshold-mixed', bundle(mixed), 0, wrapper=True)
    for count in (MASK // 65, MASK // 65 + 1, MASK):
        add('count-overflow-boundary', b'', count)
    for _ in range(random_cases):
        chosen = rng.sample(range(6), rng.randrange(1, 7))
        items = [signed(i, prefixed=bool(rng.randrange(2)), high_s=bool(rng.randrange(2)))
                 if rng.randrange(2) else approved(MEMBERS[i]) for i in chosen]
        add('random-valid', bundle(items), len(items))
        add('random-duplicate', bundle(items + [items[0]]), len(items) + 1)
    rows = [{'args': [str(x) for x in args], 'output': [str(x) for x in output]}
            for args, output in sorted(oracle.recoveries.items())]
    return calls, rows, expectations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--context', type=int, choices=(0, 1, 2), default=0)
    parser.add_argument('--random-cases', type=int, default=16)
    args = parser.parse_args()
    if args.random_cases < 0:
        parser.error('--random-cases must be nonnegative')
    return campaign(args.output, fixture=FIXTURE, driver_template=DRIVER,
        make_transactions=transactions, initial_storage=initial_storage,
        storage_fields=args.context + 3, context=args.context,
        optimized=args.optimized, random_cases=args.random_cases)


if __name__ == '__main__':
    sys.exit(main())
