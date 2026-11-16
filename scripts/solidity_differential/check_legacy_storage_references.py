"""Packed legacy storage aliases: independent words, alias effects and rollback."""
import argparse
import json
from pathlib import Path

from eth_utils import keccak
from eth_abi import encode
from .engine import HarnessError, write_json
from .check_legacy_signed_scalars import signed
from .check_legacy_state_transitions import campaign, word, error, event, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyStorageReferences.sol')
FUNCTIONS = ('read()', 'edit(int24,bool)', 'interleave(int24)')
MASK = (1 << 256) - 1


def scenario(kind, caller, layout, **_):
    fields = {}
    for row in layout['storage']:
        for member in layout['types'][row['type']]['members']:
            width = 8 * int(layout['types'][member['type']]['numberOfBytes'])
            fields[row['label'] + '.' + member['label']] = (
                int(row['slot']) + int(member['slot']), 8 * int(member['offset']), width)
    if 'second.delta' not in fields:
        fields.update({'second.' + name.split('.')[1]: value
                       for name, value in list(fields.items()) if name.startswith('first.')})
    state = {slot: MASK ^ (0x1234 << 200) for slot, _, _ in fields.values()}
    state[9999] = 0xABCDE

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

        def update(name, delta):
            put(name + '.delta', get(name + '.delta') + delta)
            put(name + '.afterValue', get(name + '.afterValue') + 1)

        if signature == 'edit(int24,bool)':
            delta = signed(args[0], 24)
            update('first', delta)
            value = signed(get('first.delta'), 24)
            logs = [event(caller, 'Changed(int24,uint16)', ['int24', 'uint16'],
                          [value, get('first.afterValue')])]
            logs.append({'address': caller, 'topics': [
                '0x' + keccak(text='Indexed(int24,int256)').hex(),
                '0x' + encode(['int24'], [value]).hex(),
                '0x' + encode(['int256'], [delta]).hex()], 'data': '0x'})
            logs.append(event(caller, 'Widened(int256,int24)', ['int256', 'int24'], [delta, -1]))
            values = [value]
            if args[1]:
                failure = 'rollback'
                state, logs = before, []
        elif signature == 'interleave(int24)':
            delta = signed(args[0], 24)
            update('first', delta)
            update('second', signed(-delta, 24))
            update('first', delta)
            values = [signed(get(name + '.delta'), 24) for name in ('first', 'second')]
        else:
            values = [value for name in ('first', 'second') for value in
                      (signed(get(name + '.delta'), 24), get(name + '.afterValue'))]
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
    for value in (1, -1, 0, 1 << 23, (1 << 23) - 1, (1 << 200) + 7):
        for signature, args in [('edit(int24,bool)', [value, 0]),
                                ('edit(int24,bool)', [value, 1]),
                                ('interleave(int24)', [value])]:
            add(signature, args)
            add('read()', [])
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--single-storage', action='store_true')
    parser.add_argument('--mutation', choices=['wrong-alias', 'neighbor-clobber', 'drop-revert'])
    args = parser.parse_args()
    if args.single_storage and args.mutation:
        parser.error('mutations require the distinct-record baseline')
    fixture = FIXTURE
    if args.mutation or args.single_storage:
        source = fixture.read_text()
        if args.single_storage:
            source = source.replace('    Record private second;\n', '').replace('second', 'first')
        anchors = {
            'wrong-alias': ('Record storage aliasRow = row;', 'Record storage aliasRow = second;'),
            'neighbor-clobber': ('row.delta = row.delta + delta;',
                                'row.delta = row.delta + delta; row.beforeValue = 0;'),
            'drop-revert': ('require(!reject, "rollback");', ''),
        }
        if args.mutation:
            old, new = anchors[args.mutation]
            if source.count(old) != 1:
                raise HarnessError('storage reference mutation anchor changed')
            source = source.replace(old, new)
        fixture = args.output.resolve().with_suffix('.sol')
        fixture.parent.mkdir(parents=True, exist_ok=True)
        with fixture.open('x') as stream:
            stream.write(source)
    result = campaign(args.output, kind='storage-references', fixture=fixture,
        contract='LegacyStorageReferences', functions=FUNCTIONS, prepared=True,
        optimized=args.optimized, optimizer_runs=800, scenario_builder=scenario)
    report = json.loads((args.output / 'results.json').read_text())
    if args.mutation:
        field = 'status' if args.mutation == 'drop-revert' else 'storage'
        witnesses = {route: [row['id'] for row in report['expectationMismatches']
            if row['route'] == route and row['field'] == field]
            for route in ('source', 'model', 'compiled')}
        if report['divergences'] or not all(witnesses.values()):
            raise HarnessError('mutation needs completed counterexamples on every route')
    elif result:
        raise HarnessError('legacy storage reference observations differ')
    write_json(args.output / 'complete.json', {'optimized': args.optimized,
                                             'singleStorage': args.single_storage,
                                             'mutation': args.mutation})


if __name__ == '__main__':
    main()
