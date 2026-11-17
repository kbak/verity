"""Require completed wrong observations for quotation and modifier-source mutations."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

from .engine import ROOT, HarnessError, command, write_json
from .mutations import snapshot, release


def run(output, modifiers=False):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    relative = Path('Compiler/SolidityImport/' +
                    ('ObservedImport.lean' if modifiers else 'ObservedCommand.lean'))
    source = (ROOT / relative).read_text()
    before = '| .leaveCall => `(ControlFlow.Program.leaveCall)'
    after = ('| .leaveCall => `(ControlFlow.Program.atom '
             '(Compiler.CompilationModel.Stmt.letVar "__dropped_return" '
             '(Compiler.CompilationModel.Expr.literal 0)))')
    if modifiers:
        before = 'post.toList.map Program.atom'
        after = '[]'
    if source.count(before) != 1:
        raise HarnessError('observed quotation mutation anchor changed')
    directory = output / 'snapshot'
    snapshot(directory)
    env = os.environ | {'PYTHONPATH': str(directory/'scripts') + os.pathsep +
                        os.environ.get('PYTHONPATH', ''), 'PYTHONDONTWRITEBYTECODE': '1'}

    def campaign(name):
        campaign = (['solidity_differential.check_observed_modifiers'] if modifiers else
                    ['solidity_differential.check_observed_storage', '--ordinary-import'])
        result = subprocess.run([sys.executable, '-m', *campaign,
            '--output', str(directory/'.lake'/name)], cwd=directory, env=env,
            capture_output=True, text=True, timeout=600)
        (output/(name+'.log')).write_text(result.stdout + result.stderr)
        report = directory/'.lake'/name/'results.json'
        if not report.exists():
            raise HarnessError(f'{name}: no completed report; tool failures cannot detect a mutation')
        return result.returncode, json.loads(report.read_text())

    try:
        code, baseline = campaign('baseline')
        if code or not baseline['passed']:
            raise HarnessError('unmodified observed import control failed')
        (directory/relative).write_text(source.replace(before, after))
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.ObservedCommand',
                 'Compiler.SolidityImport.ObservedExecution',
                 '--project-dir', str(directory)], cwd=directory, timeout=600,
                log=output/'build.log')
        code, report = campaign('mutated')
        witnesses = []
        for row in report['observations']:
            if row['source'] != row['case']['expected']:
                raise HarnessError('original Solidity changed under quotation mutation')
            if (row['model'] == row['generated'] and row['model'] != row['source']
                    and row['model']['status'] in ('ok', 'revert')):
                witnesses.append(row['case']['id'])
        old = json.loads((directory/'.lake/baseline/manifest.json').read_text())
        new = json.loads((directory/'.lake/mutated/manifest.json').read_text())
        if old['solcSha256'] != new['solcSha256'] or {
                p for p in old['implementation']
                if old['implementation'][p] != new['implementation'].get(p)} != {str(relative)}:
            raise HarnessError('mutation changed more than the intended quotation source')
        original_digest = json.loads((directory/'.lake/baseline/model.json').read_text())['sourceDigest']
        mutated_digest = json.loads((directory/'.lake/mutated/model.json').read_text())['sourceDigest']
        if original_digest == mutated_digest:
            raise HarnessError('provenance omitted the mutated command quotation source')
        if code != 1 or report['passed'] or not witnesses:
            raise HarnessError('quotation mutation needs completed matching wrong outcomes')
        write_json(output/'complete.json', dict(status='detected', baselinePassed=True,
            mutation='modifier-post-dropped' if modifiers else 'quoted-helper-return-dropped',
            witnesses=witnesses))
    finally:
        release(directory)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--modifiers', action='store_true')
    run(**vars(parser.parse_args()))
