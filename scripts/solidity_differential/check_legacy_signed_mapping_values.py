"""Compare narrow signed mapping storage words, reads and getters with the original bytecode."""
import argparse
from pathlib import Path

from eth_utils import keccak

from .check_legacy_state_transitions import SENDER, campaign, error, word
from .engine import HarnessError

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacySignedMappingValues.sol')
STORE = 'store(uint24,int24,bool)'
READ = 'entries(uint24)'
NEGATIVE = 'negative(uint24)'
SMALL = 'bytesByKey(uint8)'
WIDE = 'wide(uint256)'
MASK = 2**256 - 1


def scenario(_kind, account, layout, **_options):
    slots = {field['label']: int(field['slot']) for field in layout['storage']}

    def slot(name, key):
        return int.from_bytes(keccak(key.to_bytes(32, 'big') + slots[name].to_bytes(32, 'big')), 'big')

    first, other = 5, 2**24 - 1
    lo, hi = -(2**23), 2**23 - 1
    wide_key = 2**220 + 9
    state = {slot('entries', first): (0xABCD << 24) | (2**24 - 1),
             slot('entries', other): (0xCAFE << 24) | hi,
             slot('bytesByKey', 255): (5 << 8) | 128,
             slot('wide', wide_key): (101 << 248) | (1 << 247),
             # All root slots and an unrelated physical word remain observable.
             **{n: 975 for n in slots.values()}, 79: 42}
    initial = [[account, word(i), word(v)] for i, v in sorted(state.items())]
    calls, expected = [], {}

    def add(signature, args):
        if signature == SMALL:
            values = [-128]
        elif signature == WIDE:
            values = [-(2**247)]
        else:
            key = slot('entries', args[0] % 2**24)
            low = state[key] % 2**24
            prior = low - 2**24 if low >= 2**23 else low
            values = [int(prior < 0) if signature == NEGATIVE else prior]
            if signature == STORE and not args[2]:
                encoded = args[1] % 2**24
                state[key] = state[key] - low + encoded
                values.append(encoded - 2**24 if encoded >= 2**23 else encoded)
        failed = signature == STORE and bool(args[2])
        data = b''.join((v & MASK).to_bytes(32, 'big') for v in args)
        ident = str(len(calls))
        calls.append(dict(id=ident, label=signature, function=signature.split('(')[0],
            args=[v & MASK for v in args], sender=SENDER, target=account, value='0x0',
            data='0x' + (keccak(text=signature)[:4] + data).hex(),
            timestamp=1000000100 + len(calls), blockNumber=2 + len(calls)))
        expected[ident] = dict(status='revert' if failed else 'ok',
            data=error('rollback') if failed else '0x' + ''.join(word(v & MASK)[2:] for v in values),
            events=[], storage=sorted([[account, word(i), word(v)] for i, v in state.items()]))

    add(SMALL, [255])
    add(WIDE, [wide_key])
    add(READ, [first])
    add(NEGATIVE, [first])
    add(STORE, [first, lo, 0])
    add(STORE, [other, -1, 0])
    add(STORE, [first, hi, 1])
    add(READ, [first])
    add(READ, [other])
    add(STORE, [first, hi, 0])
    add(NEGATIVE, [first])
    add(STORE, [first, 0, 0])
    # ABI coder v1 cleans these high bits before hashing the key or storing the value.
    add(STORE, [(1 << 240) | first, (1 << 144) | (2**24 - 2), 0])
    add(READ, [first])
    return initial, calls, expected


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    if campaign(args.output, kind='signed-mapping-values', fixture=FIXTURE, contract=FIXTURE.stem,
                functions=[STORE, READ, NEGATIVE, SMALL, WIDE], optimized=True, optimizer_runs=800,
                prepared=args.prepared, scenario_builder=scenario):
        raise HarnessError('signed mapping values differ from the expected physical words or return values')
