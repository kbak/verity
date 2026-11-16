"""Require runtime counterexamples for incorrect fixed-array stride and bounds."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from .engine import ROOT, MUTANT_BUILD_TIMEOUT, HarnessError, command, write_json
from .mutations import snapshot, release

MUTANTS = {
    'stride': ('(.mul index (.literal descriptor.wordCount))',
               '(.mul index (.literal 1))', 'storage'),
    'bounds': ('.ite (.lt index (.literal descriptor.length)) [] [failure]',
               '.ite (.le index (.literal descriptor.length)) [] [failure]', 'status'),
}


def run(output, mutation):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    before, after, field = MUTANTS[mutation]
    relative = Path('Compiler/SolidityImport/Import.lean')
    source = (ROOT / relative).read_text()
    if source.count(before) != 1:
        raise HarnessError('fixed storage array mutation anchor changed')
    directory = output / 'snapshot'
    snapshot(directory)
    env = os.environ | {'PYTHONPATH': str(directory / 'scripts') + os.pathsep +
                        os.environ.get('PYTHONPATH', ''), 'PYTHONDONTWRITEBYTECODE': '1'}

    def campaign(name):
        result = subprocess.run([sys.executable, '-m',
            'solidity_differential.check_legacy_fixed_struct_arrays',
            '--output', str(directory / '.lake' / name)], cwd=directory, env=env,
            capture_output=True, text=True, timeout=MUTANT_BUILD_TIMEOUT)
        (output / (name + '.log')).write_text(result.stdout + result.stderr)
        report = directory / '.lake' / name / 'results.json'
        if not report.exists():
            raise HarnessError(f'{name}: no completed runtime report; not a detected mutation')
        return result.returncode, json.loads(report.read_text())

    try:
        code, baseline = campaign('baseline')
        if code or baseline['divergences'] or baseline['expectationMismatches']:
            raise HarnessError('unmodified fixed storage array control failed')
        (directory / relative).write_text(source.replace(before, after))
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.SequenceRunner', '--project-dir', str(directory)],
                cwd=directory, timeout=MUTANT_BUILD_TIMEOUT, log=output / 'build.log')
        code, report = campaign('mutated')
        mismatches = report['expectationMismatches']
        witnesses = {route: [row['id'] for row in mismatches
                            if row['route'] == route and row['field'] == field]
                     for route in ('model', 'compiled')}
        if code != 1 or not report['divergences'] or not all(witnesses.values()) or any(
                row['route'] == 'source' for row in mismatches):
            raise HarnessError('mutant needs matching source and completed model/compiled counterexamples')
        write_json(output / 'complete.json', {'mutation': mutation, 'status': 'detected',
                                              'baselinePassed': True, 'witnesses': witnesses})
    finally:
        release(directory)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--mutation', choices=tuple(MUTANTS), required=True)
    run(**vars(parser.parse_args()))
