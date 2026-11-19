"""Check physical signed-key storage slots across forwarded receivers, getters and rollback."""
import argparse
from pathlib import Path

from eth_utils import keccak

from .check_legacy_state_transitions import SENDER, campaign, error, event, word

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacySignedMappingKeys.sol')
FUNCTIONS = ('update(bool,int16,uint256,bool)', 'first(int16)', 'second(int16)',
             'store(int8,uint8)', 'narrow(int128)')
MASK = (1 << 256) - 1


def scenario(kind, caller, layout, **_):
    roots = {row['label']: int(row['slot']) for row in layout['storage']}

    def slot(name, key):
        preimage = (key & MASK).to_bytes(32, 'big') + roots[name].to_bytes(32, 'big')
        return int.from_bytes(keccak(preimage), 'big')

    keys = (-32768, -1, 0, 1, 32767)
    narrow_keys = (-128, -1, 0, 127)
    state = {root: 0x1234 + root for root in roots.values()}
    for name, bits, samples in (('first', 16, keys), ('second', 16, keys),
                                ('narrow', 128, narrow_keys)):
        for key in samples:
            location = slot(name, key)
            state[location] = (0xabcd << 200) | (location & 255)
            if key < 0:
                # A zero-extended key or an unwidened int8 input must leave its canary intact.
                state[slot(name, key % (1 << bits))] = 0x5555
                if name == 'narrow':
                    state[slot(name, key % 256)] = 0x6666

    def storage():
        return [[caller, word(k), word(v)] for k, v in sorted(state.items())]

    initial = storage()
    calls, expected = [], {}

    def add(signature, args, result, logs=(), reject=False):
        ident = str(len(calls))
        args = [v & MASK for v in args]
        encoded = keccak(text=signature)[:4] + b''.join(v.to_bytes(32, 'big') for v in args)
        calls.append(dict(id=ident, label=signature, function=signature.split('(')[0], args=args,
                          sender=SENDER, target=caller, value='0x0', data='0x' + encoded.hex(),
                          timestamp=1000000100 + len(calls), blockNumber=2 + len(calls)))
        expected[ident] = dict(status='revert' if reject else 'ok',
                               data=error('rollback') if reject else word(result),
                               events=list(logs), storage=storage())

    update, first, second, store, narrow = FUNCTIONS
    for key in keys:
        # The legacy v1 decoder accepts dirty signed words. Only the declared low bits matter.
        dirty_key = (1 << 200) | (key % (1 << 16))
        for name, getter in (('first', first), ('second', second)):
            location = slot(name, key)
            add(getter, [dirty_key], state[location])
            for mask, reject in ((1 << 255, False), (255, True), (1 << 255, False)):
                logs = []
                if not reject:
                    state[location] ^= mask
                    logs = [event(caller, 'Changed(uint256)', ['uint256'], [state[location]])]
                add(update, [name == 'second', dirty_key, mask, reject], state[location], logs, reject)
                add(getter, [key], state[location])
    for i, key in enumerate(narrow_keys):
        location = slot('narrow', key)
        amount = (i + 1) * 11
        state[location] = (state[location] & (MASK ^ 255)) | amount
        add(store, [(1 << 200) | (key % 256), amount], amount)
        add(narrow, [key], amount)
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    args = parser.parse_args()
    return campaign(args.output, kind='signed-mapping-keys', fixture=FIXTURE,
                    contract='LegacySignedMappingKeys', functions=FUNCTIONS, prepared=True,
                    optimized=args.optimized, optimizer_runs=800, scenario_builder=scenario)


if __name__ == '__main__':
    raise SystemExit(main())
