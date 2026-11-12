"""Completed three-route counterexamples for raw static helper guard mutations."""
import argparse
import json
from pathlib import Path
from .engine import HarnessError, write_json
from .check_legacy_signature_calls import campaign
from .check_legacy_static_words import FIXTURE, MODEL, transactions

MUTANTS = {
    'success-guard': ('require(success && data.length >= 32);', 'require(data.length >= 32);'),
    'decoder-length': ('require(success);\n        return abi.decode(data, (uint256));',
        'require(success);\n        uint256 answer;\n'
        '        assembly { answer := mload(add(data, 32)) }\n        return answer;'),
    'minimum-guard': ('require(observed >= minimum, "insufficient");', '')}


def witness_transactions(names):
    def selected(seed, caller, accounts, random_cases):
        rows, recoveries, expected = transactions(seed, caller, accounts, 0)
        predicates = {
            'success-guard': lambda tx: tx['function'] == 'word' and tx['args'][0] == int(accounts[10], 16),
            'decoder-length': lambda tx: tx['function'] == 'decoded' and tx['args'][0] == int(accounts[6], 16),
            'minimum-guard': lambda tx: tx['function'] == 'atLeast' and tx['args'][0] == int(accounts[0], 16)
                                      and expected[tx['id']][0] == 'revert'}
        witnesses = [next(tx for tx in rows if predicates[name](tx)) for name in names]
        witnesses.sort(key=lambda tx: tx["blockNumber"])
        if any(expected[tx['id']][0] != 'revert' for tx in witnesses):
            raise HarnessError('mutation witness lacks original rejection')
        return witnesses, recoveries, {tx['id']: expected[tx['id']] for tx in witnesses}
    return selected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    if campaign(out / 'baseline', optimized=args.optimized, fixture=FIXTURE, driver_template=MODEL,
                make_transactions=witness_transactions(MUTANTS)):
        raise HarnessError('unmodified mutation witnesses failed')
    source = FIXTURE.read_text()
    results = []
    for name, (before, after) in MUTANTS.items():
        if source.count(before) != 1:
            raise HarnessError('nonunique raw static mutation anchor: ' + name)
        folder = out / name
        folder.mkdir()
        fixture = folder / FIXTURE.name
        fixture.write_text(source.replace(before, after))
        status = campaign(folder / 'run', optimized=args.optimized, fixture=fixture,
                          driver_template=MODEL, make_transactions=witness_transactions([name]))
        report = json.loads((folder / 'run/campaign.json').read_text())
        mismatches = report['expectationMismatches']
        if status != 1 or report['divergences'] or len(mismatches) != 3 or \
                {row['route'] for row in mismatches} != {'source', 'model', 'compiled'} or \
                any(row['actual'][0] != 'ok' or row['expected'][0] != 'revert' for row in mismatches):
            raise HarnessError('missing completed guard counterexample: ' + name)
        results.append({'mutant': name, 'detected': True, 'routes': 3,
                        'witness': mismatches[0]['id'], 'baselinePassed': True})
    write_json(out / 'complete.json', {'mutants': results, 'optimized': args.optimized})
    print(f'{len(results)} raw static source mutants detected on all three routes')


if __name__ == '__main__':
    main()
