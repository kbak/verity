"""Mixed storage/scalar tuples preserve addresses, captured values and packed words."""
import argparse
import json
from pathlib import Path

from eth_utils import keccak
from .engine import HarnessError, write_json
from .check_legacy_signed_scalars import signed
from .check_legacy_state_transitions import campaign, word, error, event, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyMixedStorageReturns.sol')
EDITS = ('edit', 'namedEdit', 'assignedEdit', 'middleEdit', 'conditionalEdit',
         'defaultEdit', 'reboundEdit')
FUNCTIONS = ('read()', *(name + '(bool,int24,bool)' for name in EDITS),
             'dropEdit(bool,int24)', 'pairEdit(bool,int24)', 'guardedEdit(bool,int24,bool,bool)')
MASK = (1 << 256) - 1


def scenario(kind, caller, layout, **_):
    fields = {}
    for row in layout['storage']:
        for member in layout['types'][row['type']]['members']:
            width = 8 * int(layout['types'][member['type']]['numberOfBytes'])
            fields[row['label'] + '.' + member['label']] = (
                int(row['slot']) + int(member['slot']), 8 * int(member['offset']), width)
    state = {slot: MASK ^ (0x4321 << 200) for slot, _, _ in fields.values()}
    state[9999] = 0xABCDEF

    def get(name):
        slot, shift, width = fields[name]
        return (state[slot] >> shift) & ((1 << width) - 1)

    def put(name, value):
        slot, shift, width = fields[name]
        mask = ((1 << width) - 1) << shift
        state[slot] = (state[slot] & (MASK ^ mask)) | ((value << shift) & mask)

    put('first.delta', (1 << 23) - 1)
    put('second.delta', 1 << 23)
    initial = [[caller, word(k), word(v)] for k, v in sorted(state.items())]
    calls, expected = [], {}

    def add(signature, args):
        nonlocal state
        before, logs, failure = dict(state), [], None
        if signature == 'read()':
            values = [value for name in ('first', 'second') for value in
                      (signed(get(name + '.delta'), 24), get(name + '.afterValue'))]
        else:
            target = 'second' if args[0] else 'first'
            neighbor = 'first' if args[0] else 'second'
            step = signed(args[1], 24)
            previous = signed(get(target + '.delta'), 24)
            count = get(target + '.afterValue')
            if signature.startswith('dropEdit('):
                put('first.delta', get('first.delta') + step)
                values = [previous, signed(get('first.delta'), 24)]
            elif signature.startswith('pairEdit('):
                put(target + '.delta', get(target + '.delta') + step)
                put(neighbor + '.delta', get(neighbor + '.delta') - step)
                values = [previous, signed(get(target + '.delta'), 24),
                          signed(get(neighbor + '.delta'), 24)]
            else:
                guarded = signature.startswith('guardedEdit(')
                if guarded:
                    put('first.afterValue', get('first.afterValue') + 3)
                put(target + '.delta', get(target + '.delta') + step)
                put(target + '.afterValue', get(target + '.afterValue') + 1)
                if signature.startswith('defaultEdit('):
                    previous, count = 0, 0
                elif signature.startswith('reboundEdit('):
                    slot, shift, width = fields['first.delta']
                    previous = signed((before[slot] >> shift) & ((1 << width) - 1), 24)
                values = [previous, signed(get(target + '.delta'), 24), count]
                logs = [event(caller, 'Mixed(int24,int24,uint16)',
                              ['int24', 'int24', 'uint16'], values)]
                if (guarded and not args[3]) or args[2]:
                    failure = 'guard' if guarded and not args[3] else 'rollback'
                    state, logs = before, []
        ident = str(len(calls))
        raw = b''.join((v & MASK).to_bytes(32, 'big') for v in args)
        calls.append(dict(id=ident, label=signature, function=signature.split('(')[0],
            args=[v & MASK for v in args], sender=SENDER, target=caller, value='0x0',
            data='0x' + (keccak(text=signature)[:4] + raw).hex(),
            timestamp=1000000100 + len(calls), blockNumber=2 + len(calls)))
        expected[ident] = dict(status='revert' if failure else 'ok',
            data=error(failure) if failure else '0x' + ''.join(word(v & MASK)[2:] for v in values),
            events=logs, storage=[[caller, word(k), word(v)] for k, v in sorted(state.items())])

    add('read()', [])
    for value in (1, -1, 1 << 23, (1 << 23) - 1, (1 << 200) + 7):
        for other in (0, 1):
            for name in EDITS:
                for reject in (0, 1):
                    add(name + '(bool,int24,bool)', [other, value, reject])
            for allowed, reject in ((1, 0), (0, 0), (1, 1)):
                add('guardedEdit(bool,int24,bool,bool)', [other, value, reject, allowed])
            add('dropEdit(bool,int24)', [other, value])
            add('pairEdit(bool,int24)', [other, value])
            add('read()', [])
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--mutation', choices=['wrong-reference', 'lost-scalar',
                                              'neighbor-clobber', 'drop-revert'])
    args = parser.parse_args()
    fixture = FIXTURE
    if args.mutation:
        source = fixture.read_text()
        anchors = {
            'wrong-reference': ('if (other) return (second, second.delta, second.afterValue);',
                                'if (other) return (first, second.delta, second.afterValue);'),
            'lost-scalar': ('previous = row.delta;\n        count = row.afterValue;',
                            'previous = 0;\n        count = row.afterValue;'),
            'neighbor-clobber': ('aliasRow.delta = aliasRow.delta + step;',
                                'aliasRow.delta = aliasRow.delta + step; aliasRow.beforeValue = 0;'),
            'drop-revert': ('require(!reject, "rollback");', ''),
        }
        old, new = anchors[args.mutation]
        if source.count(old) != 1:
            raise HarnessError('mixed return mutation anchor changed')
        fixture = args.output.resolve().with_suffix('.sol')
        fixture.parent.mkdir(parents=True, exist_ok=True)
        with fixture.open('x') as stream:
            stream.write(source.replace(old, new))
    result = campaign(args.output, kind='mixed-storage-returns', fixture=fixture,
        contract='LegacyMixedStorageReturns', functions=FUNCTIONS, prepared=True,
        optimized=args.optimized, optimizer_runs=800, scenario_builder=scenario)
    report = json.loads((args.output / 'results.json').read_text())
    if args.mutation:
        field = {'drop-revert': 'status', 'lost-scalar': 'data'}.get(args.mutation, 'storage')
        witnesses = {route: [row['id'] for row in report['expectationMismatches']
            if row['route'] == route and row['field'] == field]
            for route in ('source', 'model', 'compiled')}
        if report['divergences'] or not all(witnesses.values()):
            raise HarnessError('mutation needs completed counterexamples on every route')
    elif result:
        raise HarnessError('mixed storage/scalar return observations differ')
    write_json(args.output / 'complete.json', {'optimized': args.optimized,
                                             'mutation': args.mutation})


if __name__ == '__main__':
    main()
