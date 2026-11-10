"""The state oracle must detect intentional source defects on all three routes."""
import argparse
import hashlib
import json
from pathlib import Path

from .check_legacy_state_transitions import FIXTURE, campaign
from .engine import HarnessError, write_json

MUTATIONS = {
    'self-context': ('require(msg.sender == address(this), "context");', '',
                     'unauthorized-threshold', 'status'),
    'zero-bound': ('require(next != 0, "zero");', '', 'limit-0', 'status'),
    'upper-bound': ('require(next <= count, "bound");', '', 'limit-4', 'status'),
    'mapping-link': ('links[address(1)] = key;', '', 'insert-same-limit', 'storage'),
}


def run(output):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    if campaign(output / 'control'):
        raise HarnessError('unmodified state-transition control failed')
    original = FIXTURE.read_text()
    reports = []
    for name, (before, after, label, field) in MUTATIONS.items():
        if original.count(before) != 1:
            raise HarnessError('mutation anchor drifted: ' + name)
        mutated = original.replace(before, after)
        fixture = output / f'{name}.sol'
        fixture.write_text(mutated)
        result = campaign(output / name, fixture=fixture)
        report = json.loads((output / name / 'results.json').read_text())
        witnesses = [row for row in report['expectationMismatches'] if row['label'] == label and row['field'] == field]
        if result != 1 or report['divergences'] or {row['route'] for row in witnesses} != {'source', 'model', 'compiled'}:
            raise HarnessError('missing independent three-route witness: ' + name)
        if field == 'status' and any(row['expected'] != 'revert' or row['actual'] != 'ok' for row in witnesses):
            raise HarnessError('mutation did not demonstrate forbidden success: ' + name)
        reports.append({'mutant': name, 'detected': True, 'baselinePassed': True,
            'kind': 'source defect detected by independent state/event oracle', 'witnessLabel': label,
            'witnessField': field, 'witnesses': witnesses, 'original': before, 'replacement': after,
            'originalSha256': hashlib.sha256(original.encode()).hexdigest(),
            'mutantSha256': hashlib.sha256(mutated.encode()).hexdigest()})
    write_json(output / 'summary.json', {'passed': True, 'mutants': reports})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    run(parser.parse_args().output)
