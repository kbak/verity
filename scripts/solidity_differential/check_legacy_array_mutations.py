"""Source defect controls must violate unchanged requirements in all three routes."""
import argparse
import json
from pathlib import Path

from .check_legacy_address_arrays import FIXTURE, FUNCTIONS, scenario
from .check_legacy_state_transitions import campaign
from .engine import HarnessError, command, write_json

MUTATIONS = {
    'missing-membership-guard': ('require(links[item] == address(0), "duplicate");', ''),
    'missing-threshold-bound': ('require(requested <= items.length, "bound");', ''),
    'missing-list-links': ('links[prior] = item;', ''),
}


def run(output, prepared=False):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.SequenceRunner', '--project-dir', '.'],
                timeout=1800, log=output / 'build.log')
    reports = []
    for name, change in [('control', None), *MUTATIONS.items()]:
        source = FIXTURE.read_text()
        if change:
            old, new = change
            if source.count(old) != 1:
                raise HarnessError('mutation site changed')
            source = source.replace(old, new)
        fixture = output / f'{name}.sol'
        fixture.write_text(source)
        code = campaign(output / name, kind='arrays', fixture=fixture, contract='LegacyAddressArrays',
                        functions=FUNCTIONS, scenario_builder=scenario, prepared=True)
        result = json.loads((output / name / 'results.json').read_text())
        mismatches = result['expectationMismatches']
        if result['divergences']:
            raise HarnessError('source mutation has cross-route divergence')
        if change is None:
            if code or mismatches:
                raise HarnessError('unmodified control failed')
        elif code != 1 or {m['route'] for m in mismatches} != {'source', 'model', 'compiled'}:
            raise HarnessError('mutant lacks an independent-oracle witness on every route')
        reports.append({'case': name, 'passed': True, 'witnesses': mismatches})
    write_json(output / 'results.json', {'passed': True, 'cases': reports})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()))
