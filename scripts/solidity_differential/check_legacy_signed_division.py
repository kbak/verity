"""Compare admitted signed operations with Solidity bytecode and independent expectations."""
import argparse
import json
from pathlib import Path

from eth_abi import encode
from eth_utils import keccak

from .check_legacy_signed_division_source import FIXTURE, cases
from .check_legacy_state_transitions import SENDER, campaign, word
from .engine import HarnessError

# choose() deliberately divides by an unguarded parameter; its INVALID controls are source-only.
ADMITTED = [row for row in cases() if row[0].split('(')[0] != 'choose']
FUNCTIONS = list(dict.fromkeys(row[0] for row in ADMITTED))


def scenario(kind, caller, layout, **_):
    initial = [[caller, word(9999), word(0xC0FFEE)]]
    calls, expected = [], {}
    for signature, arguments, status, values in ADMITTED:
        function, types = signature[:-1].split('(')
        raw = encode(types.split(','), arguments)
        ident = str(len(calls))
        calls.append(dict(id=ident, label=signature, function=function, sender=SENDER,
            target=caller, value='0x0', timestamp=1000000100 + len(calls),
            blockNumber=2 + len(calls), data='0x' + (keccak(text=signature)[:4] + raw).hex(),
            args=[int.from_bytes(raw[i:i+32], 'big') for i in range(0, len(raw), 32)]))
        expected[ident] = dict(status=status, data='0x' + encode(['int256'] * len(values), values).hex(),
                               events=[], storage=initial)
    return initial, calls, expected


def run(output, optimized, prepared, mutations):
    output.mkdir(parents=True, exist_ok=False)

    def compare(directory, fixture):
        return campaign(directory, kind='signed-division', contract=FIXTURE.stem,
                        fixture=fixture, functions=FUNCTIONS, scenario_builder=scenario,
                        optimized=optimized, optimizer_runs=800, prepared=prepared)

    if compare(output / 'baseline', FIXTURE):
        raise HarnessError('signed division baseline disagrees with the integer expectations')
    if not mutations:
        return
    source = FIXTURE.read_text()
    for name, old, new, field in [
        ('guard', 'require(y != 0);\n        return (', 'require(y > 0);\n        return (', 'status'),
        ('sign', '(x / y, x % y)', '(x / y, -(x % y))', 'data'),
    ]:
        if source.count(old) != 1:
            raise HarnessError(f'expected exactly one {name} mutation site')
        directory = output / name
        fixture = output / (name + '.sol')
        fixture.write_text(source.replace(old, new))
        compare(directory, fixture)
        report = json.loads((directory / 'results.json').read_text())
        witnesses = [{row['id'] for row in report['expectationMismatches']
                      if row['field'] == field and row['route'] == route
                      and row['label'] == 'guarded(int24,int24)'}
                     for route in ('source', 'model', 'compiled')]
        if report['divergences'] or not set.intersection(*witnesses):
            raise HarnessError(f'{name} mutation needs the same completed counterexample on all routes')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--prepared', action='store_true')
    parser.add_argument('--mutations', action='store_true')
    run(**vars(parser.parse_args()))
