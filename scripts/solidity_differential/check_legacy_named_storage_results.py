"""Named storage-result binding preserves following effects, aliases and actual returns."""
import argparse
from pathlib import Path

from eth_utils import keccak

from .check_legacy_state_transitions import campaign, error, event, SENDER, word
from .engine import HarnessError, write_json

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyNamedStorageResults.sol')
MASK = (1 << 256) - 1
AMOUNT = (1 << 128) - 1
FUNCTIONS = ('edit(uint256,uint128,uint8)', 'advance(uint128)', 'read(uint256)')


def scenario(kind, caller, layout, **_):
    slots = {row['label']: int(row['slot']) for row in layout['storage']}

    def leaf(key):
        return int.from_bytes(keccak((key & MASK).to_bytes(32, 'big') +
                                    slots['rows'].to_bytes(32, 'big')), 'big')

    state = {slots['pad']: 0xABCDEF, slots['rows']: 0x123456,
             slots['cursor']: 0, slots['effects']: MASK - 2, 9999: 0xDEADBEEF}
    for key in (0, 1, 2, 3, MASK):
        loc = leaf(key)
        state[loc] = (0xABCD << 200) | (254 << 128) | ((AMOUNT - key) & AMOUNT)
        state[loc + 1] = (MASK - key) & MASK
    initial = [[caller, word(k), word(v)] for k, v in sorted(state.items())]
    calls, expected = [], {}

    def amount(loc, delta):
        state[loc] = (state[loc] & (MASK ^ AMOUNT)) | ((state[loc] + delta) & AMOUNT)

    def tag(loc, delta):
        mask = 255 << 128
        value = (((state[loc] >> 128) + delta) & 255) << 128
        state[loc] = (state[loc] & (MASK ^ mask)) | value

    def add(signature, args):
        nonlocal state
        before, logs, failure = dict(state), [], False

        def log(stage, loc):
            logs.append(event(caller, 'Stage(uint8,uint128,uint256)',
                              ['uint8', 'uint128', 'uint256'],
                              [stage, state[loc] & AMOUNT, state[loc + 1]]))

        if signature == FUNCTIONS[1]:
            loc = leaf(state[slots['cursor']])
            state[slots['cursor']] = (state[slots['cursor']] + 1) & MASK
            amount(loc, args[0] & AMOUNT)
            values = [state[loc] & AMOUNT, state[slots['cursor']]]
        else:
            loc = leaf(args[0])
            if signature == FUNCTIONS[0]:
                step, mode = args[1] & AMOUNT, args[2] & 255
                original = loc
                state[slots['cursor']] = (args[0] + 1) & MASK
                amount(loc, step)
                state[loc + 1] = (state[loc + 1] + 1) & MASK
                log(1, loc)
                if mode in (1, 2):
                    state[slots['effects']] = (state[slots['effects']] + mode) & MASK
                elif mode == 4:
                    loc = leaf(args[0] + 1)
                else:
                    if mode == 3:
                        loc = leaf(args[0] + 1)
                        amount(loc, step)
                    tag(original, 1)
                    if mode == 3:
                        tag(loc, 2)
                    state[slots['effects']] = (state[slots['effects']] + 4) & MASK
                    failure = mode == 5
                    if not failure:
                        log(2, loc)
                if not failure:
                    state[loc + 1] = (state[loc + 1] + 10) & MASK
                    log(3, loc)
                    amount(loc, 1)
                    log(4, loc)
                else:
                    state, logs = before, []
            values = [state[loc] & AMOUNT, (state[loc] >> 128) & 255,
                      state[loc + 1], state[slots['effects']], state[slots['cursor']]]
        ident = str(len(calls))
        calls.append(dict(id=ident, label=signature + ':' + ','.join(map(str, args)),
            function=signature.split('(')[0], args=args, sender=SENDER, target=caller,
            value='0x0', timestamp=1000000100 + len(calls), blockNumber=2 + len(calls),
            data='0x' + (keccak(text=signature)[:4] +
                         b''.join(v.to_bytes(32, 'big') for v in args)).hex()))
        expected[ident] = dict(status='revert' if failure else 'ok',
            data=error('rollback') if failure else '0x' + ''.join(word(v)[2:] for v in values),
            events=logs, storage=[[caller, word(k), word(v)] for k, v in sorted(state.items())])

    for key in (0, 1, MASK):
        for mode in (0, 1, 2, 3, 4, 5, 3):
            add(FUNCTIONS[0], [key, AMOUNT if mode % 2 else 1, mode])
            add(FUNCTIONS[2], [key])
            add(FUNCTIONS[2], [(key + 1) & MASK])
    # ABI-v1 dirty argument cleanup must not alter branch choice or storage addresses.
    add(FUNCTIONS[0], [1, (0xABCD << 128) | 17, (0xABCD << 8) | 3])
    add(FUNCTIONS[1], [1])
    add(FUNCTIONS[1], [AMOUNT])
    for key in (0, 1, 2, 3, MASK):
        add(FUNCTIONS[2], [key])
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    args = parser.parse_args()
    code = campaign(args.output, kind='named-storage-results', fixture=FIXTURE,
        contract='LegacyNamedStorageResults', functions=FUNCTIONS, prepared=True,
        optimized=args.optimized, optimizer_runs=800, scenario_builder=scenario)
    if code:
        raise HarnessError('named storage-result effects differ from independent expectations')
    write_json(args.output / 'complete.json', {'optimized': args.optimized})


if __name__ == '__main__':
    main()
