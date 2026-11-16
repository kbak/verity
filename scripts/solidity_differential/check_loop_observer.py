"""Check generic loop observations and deliberate control-flow faults.

These are semantic-component controls, not Solidity importer mutation coverage.
Each mutant must elaborate and reach the intended executable assertion.
"""
import argparse
import hashlib
import json
from pathlib import Path

from .engine import HarnessError, run_bounded, write_json

MODEL = Path('Compiler/SolidityImport/LoopExecution.lean')
CHECKS = Path('Contracts/SolidityImportSmoke/LoopExecutionControl.lean')
MUTATIONS = {
    'continue-exits': (
        '| .normal afterBody | .continueLoop afterBody => .next afterBody',
        '| .normal afterBody => .next afterBody\n'
        '      | .continueLoop afterBody => .halt (.normal afterBody)',
        'continue skips remaining body; break skips next condition'),
    'break-continues': (
        '| .breakLoop afterBody => .halt (.normal afterBody)',
        '| .breakLoop afterBody => .next afterBody',
        'continue skips remaining body; break skips next condition'),
    'condition-failure-erased': (
        '| .halt outcome => .halt (.abrupt outcome)',
        '| .halt _ => .halt (.normal state)',
        'condition abrupt outcome skips body'),
}


def run(output, mutation=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    source, checks = MODEL.read_text(), CHECKS.read_text()
    expected_error = None
    if mutation:
        before, after, expected_error = MUTATIONS[mutation]
        if source.count(before) != 1:
            raise HarnessError('loop observer mutation anchor changed')
        source = source.replace(before, after)
    import_line = 'import Compiler.SolidityImport.LoopExecution\n'
    if not checks.startswith(import_line):
        raise HarnessError('loop observer control import changed')
    # A private input validates the exact edited declarations without modifying
    # shared source or build interfaces. Keep the proofs in every mutant input.
    driver = output / 'Observer.lean'
    driver.write_text(source + '\n' + checks.removeprefix(import_line) + '\n#eval main\n')
    result = run_bounded(['turbo-lean', '--json', 'eval', str(driver),
        '--project-dir', '.', '--timeout-ms', '180000'], timeout=240)
    log = result.stdout + result.stderr
    (output / 'evaluation.log').write_text(log)
    try:
        report = json.loads(result.stdout)
    except ValueError as exc:
        raise HarnessError('missing structured loop evaluation result') from exc
    if mutation:
        # An elaboration/tool failure is not a detected control fault.
        errors = report.get('errors', [])
        passed = (result.returncode != 0 and report.get('ok') is False
                  and report.get('import_ok') is True and len(errors) == 1
                  and expected_error + ': expected' in errors[0] and 'got ' in errors[0]
                  and report.get('timed_out') is False and report.get('crashed') is False)
    else:
        passed = (result.returncode == 0 and report.get('ok') is True
                  and report.get('errors') == [] and 'loop observer controls passed' in log)
    write_json(output / 'results.json', {'passed': passed, 'mutation': mutation,
        'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest(),
        'evaluation': report, 'expectedAssertion': expected_error,
        'scope': 'loop semantic component only; no importer admission claim'})
    if not passed:
        raise HarnessError('loop observer control did not produce its required result')
    print('loop observer control passed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--mutation', choices=tuple(MUTATIONS))
    run(**vars(parser.parse_args()))
