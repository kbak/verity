"""Detect duplicate acceptance after weakening a strict ordered-record guard.

This is a source/property mutation, not an importer-equivalence mutation: all
three routes may agree on the bug. The independent authorization oracle stays
unchanged, and an unmutated positive control must pass first.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys

from .check_legacy_signature_calls import campaign
from .check_legacy_ordered_signatures import FIXTURE, DRIVER, initial_storage, transactions
from .engine import HarnessError, write_json

LABELS = {'distinct-recovered', 'all-four-modes', 'threshold-mixed',
          'duplicate-signer', 'contract-duplicate', 'invalid-member-executor', 'zero-member-executor'}
DUPLICATES = {'duplicate-signer', 'contract-duplicate'}


def selected_transactions(make_transactions, *args):
    calls, rows, expectations = make_transactions(*args)
    calls = [tx for tx in calls if tx.get('label') in LABELS]
    return calls, rows, {tx['id']: expectations[tx['id']] for tx in calls}


def run(directory, *, fixture=FIXTURE, driver_template=DRIVER, storage_fields=3,
        seed_storage=initial_storage, make_transactions=transactions, extra_sources=None,
        source_name=None, original='current <= previous', replacement='current < previous'):
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    def selected(*args):
        return selected_transactions(make_transactions, *args)
    options = dict(fixture=fixture, driver_template=driver_template, storage_fields=storage_fields,
                   initial_storage=seed_storage, make_transactions=selected,
                   extra_sources=extra_sources, random_cases=0)
    if campaign(directory / 'control', **options) != 0:
        raise HarnessError('mutation invalid: unmodified positive control failed')
    source = fixture.read_text() if source_name is None else extra_sources[source_name]
    if source.count(original) != 1:
        raise HarnessError('mutation invalid: guard must have exactly one source occurrence')
    mutated = source.replace(original, replacement)
    if source_name is None:
        copied = directory / 'fixture' / fixture.name
        copied.parent.mkdir()
        copied.write_text(mutated)
        options['fixture'] = copied
    else:
        options['extra_sources'] = {**extra_sources, source_name: mutated}
    result = campaign(directory / 'mutant', **options)
    report = json.loads((directory / 'mutant/campaign.json').read_text())
    failures = report['expectationMismatches']
    if result != 1 or report['divergences'] or not failures:
        raise HarnessError('mutation not detected as an independent authorization violation')
    if any(row['label'] not in DUPLICATES | {'zero-member-executor'} or row['expected'][0] != 'revert'
           or row['actual'][0] != 'ok' for row in failures):
        raise HarnessError('mutation invalid: failure is not duplicate-signature acceptance')
    witnesses = {row['id'] for row in failures if row['label'] in DUPLICATES}
    zero_witnesses = {row['id'] for row in failures if row['label'] == 'zero-member-executor'}
    if not witnesses:
        raise HarnessError('mutation did not demonstrate duplicate acceptance')
    for ident in witnesses | zero_witnesses:
        if {row['route'] for row in failures if row['id'] == ident} != {'source', 'model', 'compiled'}:
            raise HarnessError('mutation invalid: witness does not reproduce on all routes')
    calls = json.loads((directory / 'mutant/transactions.json').read_text())
    threshold_witnesses = {tx['id'] for tx in calls
                           if tx['id'] in witnesses and tx['function'] == 'checkThreshold'}
    explicit_witnesses = witnesses - threshold_witnesses
    if not threshold_witnesses or not explicit_witnesses:
        raise HarnessError('mutation must demonstrate duplicates in both entrypoints')
    write_json(directory / 'summary.json', {'detected': True,
        'kind': 'source mutation checked by independent authorization property',
        'original': original, 'replacement': replacement, 'witnessCaseIds': sorted(witnesses),
        'zeroAddressWitnessCaseIds': sorted(zero_witnesses),
        'thresholdWitnessCaseIds': sorted(threshold_witnesses),
        'explicitCountWitnessCaseIds': sorted(explicit_witnesses),
        'controlCases': json.loads((directory / 'control/summary.json').read_text())['count'],
        'originalSha256': hashlib.sha256(source.encode()).hexdigest(),
        'mutantSha256': hashlib.sha256(mutated.encode()).hexdigest()})
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    return run(args.output)


if __name__ == '__main__':
    sys.exit(main())
