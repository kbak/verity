"""Signed packed bytes, physical memory and mapping keys against independent expectations."""
import argparse
from pathlib import Path

from eth_utils import keccak

from .check_legacy_byte_pointers import Memory, ok
from .check_legacy_packed_hash import packed
from .check_legacy_state_transitions import campaign, error, event, SENDER, word
from .engine import HarnessError, write_json

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacySignedPackedHash.sol')
MASK = (1 << 256) - 1
AMOUNT = (1 << 128) - 1
WIDTH_GROUPS = ('widthsLow', 'widthsMiddle', 'widthsHigh', 'widthsFull')
HASH_FUNCTIONS = ('key(address,int24,int24)', 'unsignedKey(address,uint24,uint24)',
    'inspect(address,int24,int24,uint256)', 'chain(address,int24,int24,uint256)',
    *(name + '(int256)' for name in WIDTH_GROUPS))
MAPPING_FUNCTIONS = ('read(address,int24,int24)', 'edit(address,int24,int24,uint128,bool)')


def signed_bytes(raw, width):
    """Interpret the declared-width two's-complement integer before encoding it."""
    modulus = 1 << (8 * width)
    value = raw % modulus
    if value >= modulus // 2:
        value -= modulus
    return value.to_bytes(width, 'big', signed=True)


def key_parts(account, left, right):
    return [(account % (1 << 160)).to_bytes(20, 'big'),
            signed_bytes(left, 3), signed_bytes(right, 3)]


def inputs():
    values = (0, 1, -1, -(1 << 23), (1 << 23) - 1, -7)
    rows = [(1, left & MASK, right & MASK) for left, right in zip(values, reversed(values))]
    # Same low values with noncanonical ABI-v1 upper bits, including the sign boundary.
    rows += [(1 | (0xAB << 200), (0x1234 << 24) | 0xFFFFFF, (0xABCD << 24) | 1),
             ((1 << 160) - 1, (0xFFFF << 24) | 0x800000, (0x1234 << 24) | 0x7FFFFF)]
    return rows


def transaction(caller, calls, signature, args):
    ident = str(len(calls))
    args = [value & MASK for value in args]
    raw = b''.join(value.to_bytes(32, 'big') for value in args)
    calls.append(dict(id=ident, label=signature, function=signature.split('(')[0], args=args,
        sender=SENDER, target=caller, value='0x0',
        data='0x' + (keccak(text=signature)[:4] + raw).hex(),
        timestamp=1000000100 + len(calls), blockNumber=2 + len(calls)))
    return ident


def hash_scenario(kind, caller, layout, **_):
    calls, expected = [], {}

    def add(signature, args, *values):
        ident = transaction(caller, calls, signature, args)
        status, data = ok(*values)
        expected[ident] = dict(status=status, data=data, events=[], storage=[])

    offsets = (0, 1, 31, 32, 49, 51, 52, 54, 55, 57, 58, 63, 64, 65, 88, 96, 124)
    for account, left, right in inputs():
        parts = key_parts(account, left, right)
        digest = keccak(b''.join(parts))
        add(HASH_FUNCTIONS[0], [account, left, right], int.from_bytes(digest, 'big'))
        add(HASH_FUNCTIONS[1], [account, left, right], int.from_bytes(digest, 'big'))
        memory = Memory([])
        assert packed(memory, parts) == digest
        for offset in offsets:
            add(HASH_FUNCTIONS[2], [account, left, right, offset],
                int.from_bytes(digest, 'big'), memory.load(64), memory.load(128 + offset))
        memory = Memory([])
        first = packed(memory, parts)
        second = packed(memory, [first, signed_bytes(right, 3)])
        for offset in offsets:
            add(HASH_FUNCTIONS[3], [account, left, right, offset],
                int.from_bytes(second, 'big'), memory.load(64), memory.load(128 + offset))
    for value in (0, 1, -1, -(1 << 255), (1 << 255) - 1,
                  0x800000, 0x7FFFFF, 0x123456789ABCDEF, -(1 << 23)):
        for group, name in enumerate(WIDTH_GROUPS):
            payload = b''.join(signed_bytes(value, width)
                               for width in range(1 + group * 8, 9 + group * 8))
            add(name + '(int256)', [value], int.from_bytes(keccak(payload), 'big'))
    return [], calls, expected


def mapping_scenario(kind, caller, layout, **_):
    root = next(int(row['slot']) for row in layout['storage'] if row['label'] == 'rows')

    def location(args):
        key = keccak(b''.join(key_parts(*args[:3])))
        return int.from_bytes(keccak(key + root.to_bytes(32, 'big')), 'big')

    state = {root: 0xBEEF, 9999: 0xABCD}
    for args in inputs():
        state[location(args)] = (0x1234 << 200) | (17 << 128) | AMOUNT
    initial = [[caller, word(k), word(v)] for k, v in sorted(state.items())]
    calls, expected = [], {}

    def add(signature, args):
        nonlocal state
        before, logs, failure = dict(state), [], False
        loc = location(args)
        if signature.startswith('edit('):
            amount = ((state[loc] & AMOUNT) + args[3]) & AMOUNT
            state[loc] = (state[loc] & (MASK ^ AMOUNT)) | amount
            logs = [event(caller, 'Changed(uint128)', ['uint128'], [amount])]
            values = [amount]
            failure = bool(args[4])
            if failure:
                state, logs = before, []
        else:
            values = [state[loc] & AMOUNT, (state[loc] >> 128) & 255]
        ident = transaction(caller, calls, signature, args)
        expected[ident] = dict(status='revert' if failure else 'ok',
            data=error('rollback') if failure else ok(*values)[1], events=logs,
            storage=[[caller, word(k), word(v)] for k, v in sorted(state.items())])

    for args in inputs():
        add(MAPPING_FUNCTIONS[0], list(args))
        for step, reject in ((1, 0), (AMOUNT, 0), (17, 1)):
            add(MAPPING_FUNCTIONS[1], [*args, step, reject])
            add(MAPPING_FUNCTIONS[0], list(args))
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--mapping', action='store_true')
    args = parser.parse_args()
    code = campaign(args.output, kind='signed-packed-mapping' if args.mapping else 'signed-packed',
        fixture=FIXTURE, contract='LegacySignedPackedMapping' if args.mapping else 'LegacySignedPackedHash',
        functions=MAPPING_FUNCTIONS if args.mapping else HASH_FUNCTIONS, prepared=True,
        optimized=args.optimized, optimizer_runs=800,
        scenario_builder=mapping_scenario if args.mapping else hash_scenario)
    if code:
        raise HarnessError('signed packed observations differ from independent expectations')
    write_json(args.output / 'complete.json', {'optimized': args.optimized, 'mapping': args.mapping})


if __name__ == '__main__':
    main()
