"""Compare inclusive interval exits, skipped suffixes, and exact midpoint visits."""
import argparse
import json
from pathlib import Path

from .check_legacy_word_arithmetic import check_words
from .engine import HarnessError, run_bounded

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyIntervalSearch.sol')
SEARCH = 'search(uint8,uint8,uint8,uint8,uint8)'


def vectors():
    # Final octet is the midpoint on exit. Earlier octets record every interior visit.
    for args, visits in [
        ((3, 3, 0, 0, 0), [3]),
        ((200, 100, 0, 0, 0), [22]),
        ((150, 220, 0, 0, 0), [57]),
        ((0, 1, 0, 0, 0), [0]),
        ((0, 8, 0, 4, 0), [4, 4]),
        ((0, 8, 4, 4, 4), [4, 6, 5]),
        ((0, 8, 251, 4, 4), [4, 1, 2]),
        ((0, 8, 0, 0, 0), [4, 1, 0]),
        ((0, 255, 0, 222, 0), [127, 63]),
        ((0, 126, 0, 1, 0), [63, 31, 15, 7, 3, 1, 1]),
        ((0, 126, 63, 100, 0), [63, 95, 111, 103, 99, 101, 100]),
    ]:
        yield SEARCH, args, 'ok', [int.from_bytes(bytes(visits), 'big')]
    yield SEARCH, (0, 8, 0, 4, 4), 'revert', []


def completed_wrong_trace(report):
    """Both lowered routes must finish with the same wrong bytes on a source success."""
    if any(row['route'] == 'source' for row in report['expectationMismatches']):
        return False
    observations = report['observations']
    return any(
        source['status'] == model['status'] == compiled['status'] == 'ok'
        and model['data'] == compiled['data'] != source['data']
        for source, model, compiled in zip(
            observations['source'], observations['model'], observations['compiled'], strict=True)
    )


def check_rejections(output):
    source = FIXTURE.read_text()
    cases = [
        ('unguarded', None, None, 'unguarded(uint8,uint8,uint8)', 'interval search needs progress'),
        ('weak-endpoint', 'middle <= low || middle >= high', 'middle < low || middle >= high',
         SEARCH, 'interval search needs progress'),
        ('skip-one-too-far', 'low = middle + 1;\n                continue;',
         'low = middle + 2;\n                continue;', SEARCH, 'continue must first exclude'),
        ('lost-continue', 'low = middle + 1;\n                continue;', 'low = middle + 1;',
         SEARCH, 'update a bound and continue'),
        ('clobbered-midpoint', '            trace = trace', '            ++middle;\n            trace = trace',
         SEARCH, 'intervening bound write'),
    ]
    for name, before, after, signature, reason in cases:
        directory = output / name
        directory.mkdir()
        if before is not None and source.count(before) != 1:
            raise HarnessError(f'{name}: source mutation anchor changed')
        (directory / FIXTURE.name).write_text(source if before is None else source.replace(before, after))
        driver = directory / 'Check.lean'
        driver.write_text(
            'import Compiler.SolidityImport.Import\n'
            f'solidity_import checked from "{directory}" entry "{FIXTURE.name}"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,\n'
            '          optimizerRuns := some 800, bytecodeHash := "none" }\n'
            f'  contract {FIXTURE.stem}\n  function {signature}\n')
        result = run_bounded(['turbo-lean', '--json', 'eval', str(driver),
                              '--project-dir', '.', '--timeout-ms', '90000'])
        report = json.loads(result.stdout)
        errors = report.get('errors', [])
        if report.get('ok') or report.get('timed_out') or report.get('crashed') or not any(
                FIXTURE.name in msg and '[solidity-import:unsupported]' in msg and reason in msg
                for msg in errors):
            raise HarnessError(f'{name}: expected located rejection for {reason}: {errors}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    check_words(FIXTURE, vectors(), args.output, args.prepared)
    check_rejections(args.output.resolve())
