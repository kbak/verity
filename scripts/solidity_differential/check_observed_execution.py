"""Check downstream frame boundaries; exhaustion must never fabricate success."""
import argparse
import hashlib
import json
from pathlib import Path

from .engine import ROOT, HarnessError, command, run_bounded, write_json
from .mutations import snapshot, release

DRIVER = Path('Contracts/SolidityImportSmoke/ObservedExecutionChecks.lean')
MODULE = Path('Compiler/SolidityImport/ObservedExecution.lean')


def evaluate(root, log):
    driver = root / '.lake' / (log.stem + '-execution-checks.lean')
    driver.write_text((root / DRIVER).read_text() + '\n#eval runObservedExecutionChecks\n')
    result = run_bounded(['turbo-lean', '--json', 'eval', driver,
                          '--project-dir', root, '--timeout-ms', '120000'], cwd=root, timeout=180)
    log.write_text(result.stdout + result.stderr)
    try:
        payload = json.loads(result.stdout)
    except ValueError as exc:
        raise HarnessError('missing structured adapter result') from exc
    if payload.get('timed_out') or payload.get('crashed') or not payload.get('import_ok'):
        raise HarnessError('adapter infrastructure failure')
    return result.returncode, payload


def check(output, mutation=False):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    root = output / 'snapshot' if mutation else ROOT
    if mutation:
        snapshot(root)
    try:
        code, result = evaluate(root, output / 'baseline.log')
        if code or not result['ok'] or 'OBSERVED_EXECUTION_CHECKS_OK' not in ''.join(
                result.get('messages', []) + [result.get('stdout', '')]):
            raise HarnessError('unmodified adapter did not pass')
        evidence = dict(status='passed', baselinePassed=True,
                        sourceSha256=hashlib.sha256((root / MODULE).read_bytes()).hexdigest())
        if mutation:
            source = (root / MODULE).read_text()
            before = '| none => return none'
            after = '| none => return some { success := true, data := [], world := initial }'
            if source.count(before) != 1:
                raise HarnessError('exhaustion mutation anchor changed')
            (root / MODULE).write_text(source.replace(before, after))
            command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.ObservedExecution',
                     '--project-dir', root], cwd=root, timeout=600, log=output / 'build.log')
            code, result = evaluate(root, output / 'mutated.log')
            errors = result.get('errors', [])
            if (code != 1 or result['ok'] or len(errors) != 1 or
                    not errors[0].strip().endswith('error: exhaustion published a source outcome')):
                raise HarnessError('mutation needs the completed exhaustion assertion failure')
            evidence.update(status='detected', mutation='exhaustion-fabricates-success')
        write_json(output / 'complete.json', evidence)
    finally:
        if mutation:
            release(root)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--mutation', action='store_true')
    check(**vars(parser.parse_args()))
