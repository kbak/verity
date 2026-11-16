"""Fixed storage records preserve bounds, packed neighbours and helper alias identity."""
import argparse
from pathlib import Path
from eth_utils import keccak
from .check_legacy_state_transitions import campaign, error, SENDER, word
from .engine import HarnessError, write_json

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyFixedStructArrays.sol')
MASK = (1 << 256) - 1
FUNCTIONS = ('edit(uint256,int56,uint160,bool,bool)', 'read(uint256)',
             'editOther(uint256,uint32)', 'advance(int56)', 'wide(uint256,int24,uint256,bool)')


def scenario(kind, caller, layout, **_):
    slots = {row['label']: int(row['slot']) for row in layout['storage']}
    state = {slots['pad']: 0xABCDEF, slots['cursor']: 0, slots['effects']: MASK,
             slots['wideRows'] + 9: 0xDEADBEEF}
    # Oracle offsets are specified independently of importer descriptors.
    for name in ('rows', 'other'):
        for index in (0, 1, 2, 3, 65533, 65534):
            state[slots[name] + index] = ((index + 1) | (((1 << 55) + index) << 32) |
                (((1 << 160) - index - 1) << 88) | (1 << 248))
    for index in range(3):
        slot = slots['wideRows'] + 3 * index
        state[slot] = (index + 9) | (((1 << 128) - 1) << 128)
        state[slot + 1] = (0xABCDEF << 32) | (1 << 24) | (1 << 23)
        state[slot + 2] = MASK - index
    initial = [[caller, word(k), word(v)] for k, v in sorted(state.items())]
    calls, expected = [], {}

    def bits(slot, offset, width, value):
        mask = ((1 << width) - 1) << offset
        state[slot] = (state.get(slot, 0) & (MASK ^ mask)) | ((value << offset) & mask)

    def signed(value, width):
        value &= (1 << width) - 1
        return (value - (1 << width) if value >> (width - 1) else value) & MASK

    def packed(slot):
        value = state.get(slot, 0)
        return [value & ((1 << 32) - 1), signed(value >> 32, 56),
                (value >> 88) & ((1 << 160) - 1), int(bool(value >> 248))]

    def add(which, args):
        nonlocal state
        before = dict(state)
        status, data, values = 'ok', '0x', []
        index = state[slots['cursor']] if which == 3 else args[0]
        length = 3 if which == 4 else 65535
        if which in (0, 4):
            state[slots['effects']] = (state[slots['effects']] + 1) & MASK
        if index >= length:
            status = 'invalid'
        else:
            slot = slots['other' if which == 2 else 'rows'] + index
            if which == 0:
                bits(slot, 0, 32, state.get(slot, 0) + 1)
                bits(slot, 32, 56, args[1])
                bits(slot, 88, 160, args[2])
                bits(slot, 248, 8, int(bool(args[3])))
                values = packed(slot) + [state[slots['effects']]]
            elif which == 1:
                values = packed(slot) + [65535]
            elif which == 2:
                bits(slot, 0, 32, args[1])
                values = packed(slot)[:2]
            elif which == 3:
                state[slots['cursor']] += 1
                bits(slot, 32, 56, args[0])
                values = [state[slots['cursor']], signed(args[0], 56)]
            else:
                slot = slots['wideRows'] + 3 * index
                bits(slot, 128, 128, (state[slot] >> 128) + 1)
                bits(slot + 1, 0, 24, args[1])
                bits(slot + 1, 24, 8, int(not ((state[slot + 1] >> 24) & 255)))
                state[slot + 2] = args[2]
                values = [state[slot] & ((1 << 128) - 1), state[slot] >> 128,
                          signed(state[slot + 1], 24), (state[slot + 1] >> 24) & 255,
                          state[slot + 2]]
            if which in (0, 4) and args[-1]:
                status, data = 'revert', error('rollback')
        if status != 'ok':
            state = before
        else:
            data = '0x' + ''.join(word(value)[2:] for value in values)
        signature = FUNCTIONS[which]
        ident = str(len(calls))
        calls.append(dict(id=ident, label=signature + ':' + ','.join(map(str, args)),
            function=signature.split('(')[0], args=args, sender=SENDER, target=caller,
            value='0x0', timestamp=1000000100 + len(calls), blockNumber=2 + len(calls),
            data='0x' + (keccak(text=signature)[:4] +
                         b''.join((v & MASK).to_bytes(32, 'big') for v in args)).hex()))
        expected[ident] = dict(status=status, data=data, events=[],
            storage=[[caller, word(k), word(v)] for k, v in sorted(state.items())])

    for index in (0, 1, 65534, 65535, 65536, MASK):
        add(1, [index])
        add(0, [index, 1 << 55, (1 << 160) - 1, 0, 0])
        add(0, [index, MASK, 7, 1, 1])
        add(1, [index])
        add(2, [index, (1 << 32) - 1])
    for delta in (MASK, (1 << 55) - 1, 1 << 55):
        add(3, [delta])
    for index in (0, 1, 2, 3, MASK):
        for fail in (0, 1):
            add(4, [index, MASK if fail else 1 << 23, MASK - index, fail])
    for index in (0, 1, 2):
        add(1, [index])
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    args = parser.parse_args()
    code = campaign(args.output, kind='fixed-struct-arrays', fixture=FIXTURE,
        contract='LegacyFixedStructArrays', functions=FUNCTIONS, prepared=True,
        optimized=args.optimized, optimizer_runs=800, scenario_builder=scenario)
    if code:
        raise HarnessError('fixed storage array state transitions differ from independent expectations')
    write_json(args.output / 'complete.json', {'optimized': args.optimized})


if __name__ == '__main__':
    main()
