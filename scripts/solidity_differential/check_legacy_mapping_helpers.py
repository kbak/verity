"""Whole mappings preserve helper identity, packed words, boolean reads and rollback."""
import argparse
from pathlib import Path

from eth_utils import keccak

from .engine import HarnessError, write_json
from .check_legacy_state_transitions import campaign, word, error, event, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyMappingHelpers.sol')
MASK = (1 << 256) - 1
AMOUNT = (1 << 128) - 1
KEYS = (0, 1, int.from_bytes(keccak(b'generic-mapping-key'), 'big'))


def scenario(kind, caller, layout, **_):
    single = kind == 'single'
    slots = {row['label']: int(row['slot']) for row in layout['storage']}

    def leaf(name, key):
        return int.from_bytes(keccak(key.to_bytes(32, 'big') +
                                    slots[name].to_bytes(32, 'big')), 'big')

    # Seed dirty unused bits and unrelated slots; every step observes physical words.
    state = {slot: 0xABCD + slot for slot in slots.values()} | {9999: 0x123456}
    for name in ('first',) if single else ('first', 'second'):
        for key in KEYS:
            loc = leaf(name, key)
            state[loc] = (0xABCD << 200) | ((17 + slots[name]) << 128) | AMOUNT
            state[loc + 1] = 9 + slots[name]
    if not single:
        for key in KEYS:
            state[leaf('small', key)] = (0xABCDE << 8) | 254
            state[leaf('flags', key)] = (0xFFFF << 8) | 127

    initial = [[caller, word(k), word(v)] for k, v in sorted(state.items())]
    calls, expected = [], {}

    def add(signature, args):
        nonlocal state
        before, logs, failure = dict(state), [], False
        if signature.startswith('scalar'):
            key = args[0]
            if signature.startswith('scalar('):
                for name, value in (('small', args[1] & 255), ('flags', int(bool(args[2])))):
                    loc = leaf(name, key)
                    state[loc] = (state[loc] & (MASK ^ 255)) | value
            values = [state[leaf('small', key)] & 255,
                      int(bool(state[leaf('flags', key)] & 255))]
        else:
            other, key = (0, args[0]) if single or signature == 'direct(bytes32)' else args[:2]
            loc = leaf('second' if other else 'first', key)
            previous = state[loc] & AMOUNT
            if signature.startswith('edit('):
                step, reject = args[-2:]
                current = (previous + step) & AMOUNT
                state[loc] = (state[loc] & (MASK ^ AMOUNT)) | current
                state[loc + 1] = (state[loc + 1] + 1) & MASK
                values = [previous, current, state[loc + 1]]
                logs = [event(caller, 'Changed(uint128,uint128,uint256)',
                              ['uint128', 'uint128', 'uint256'], values)]
                failure = bool(reject)
                if failure:
                    state, logs = before, []
            else:
                values = [previous, (state[loc] >> 128) & 255, state[loc + 1]]
        ident = str(len(calls))
        raw = b''.join(v.to_bytes(32, 'big') for v in args)
        calls.append(dict(id=ident, label=signature, function=signature.split('(')[0],
            args=args, sender=SENDER, target=caller, value='0x0',
            data='0x' + (keccak(text=signature)[:4] + raw).hex(),
            timestamp=1000000100 + len(calls), blockNumber=2 + len(calls)))
        expected[ident] = dict(status='revert' if failure else 'ok',
            data=error('rollback') if failure else '0x' + ''.join(word(v)[2:] for v in values),
            events=logs, storage=[[caller, word(k), word(v)] for k, v in sorted(state.items())])

    read = 'read(bytes32)' if single else 'read(bool,bytes32)'
    edit = 'edit(bytes32,uint128,bool)' if single else 'edit(bool,bytes32,uint128,bool)'
    for key in KEYS:
        for other in (0,) if single else (0, 1):
            args = [key] if single else [other, key]
            add(read, args)
            for step, reject in ((1, 0), (AMOUNT, 0), (17, 1), (3, 0)):
                add(edit, args + [step, reject])
                add(read, args)
                if not single:
                    add('direct(bytes32)', [key])
        if not single:
            add('scalarRead(uint256)', [key])
            for value, flag in ((1, 0), (255, 1), (0, 0)):
                add('scalar(uint256,uint8,bool)', [key, value, flag])
                add('scalarRead(uint256)', [key])
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--single', action='store_true')
    args = parser.parse_args()
    functions = ('read(bytes32)', 'edit(bytes32,uint128,bool)') if args.single else (
        'read(bool,bytes32)', 'edit(bool,bytes32,uint128,bool)',
        'scalarRead(uint256)', 'scalar(uint256,uint8,bool)', 'direct(bytes32)')
    code = campaign(args.output, kind='single' if args.single else 'multiple', fixture=FIXTURE,
        contract='LegacySingleMappingHelper' if args.single else 'LegacyMappingHelpers',
        functions=functions, prepared=True, optimized=args.optimized, optimizer_runs=800,
        scenario_builder=scenario)
    if code:
        raise HarnessError('whole-mapping helper observations differ')
    write_json(args.output / 'complete.json', {'optimized': args.optimized, 'single': args.single})


if __name__ == '__main__':
    main()
