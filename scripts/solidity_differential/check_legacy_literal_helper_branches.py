"""Compare helper returns and reverts, and check which helper declarations were reached."""
import argparse
import json
from pathlib import Path

from .check_legacy_word_arithmetic import check_words
from .engine import HarnessError, run_bounded

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyLiteralHelperBranches.sol')
WORD = 1 << 256


def vectors():
    for n in (0, 3, 9, 255, 256, WORD - 1):
        yield 'captured(uint256)', [n], 'ok', [(n + 11) % WORD, (n + 17) % WORD]
        yield 'selectedFallthrough(uint256)', [n], 'ok', [12 if n == 3 else (n + 5) % WORD]
        if n == 9:
            yield 'earlyPair(uint256)', [n], 'revert', []
        else:
            pair = [8, 9] if n == 3 else [n, (n + 1) % WORD]
            yield 'earlyPair(uint256)', [n], 'ok', pair
        yield 'reassigned(uint256)', [n], 'ok', [31 if n % 256 == 0 else 47]


def check_reachable_helpers(output):
    division_line, = (i for i, line in enumerate(FIXTURE.read_text().splitlines(), 1)
                      if line.strip() == 'return n / d;')
    location = f'{FIXTURE.name}:{division_line}:'
    for signature in ('earlyPair(uint256)', 'dynamicPair(uint32,uint256)', 'liveFallback(uint256)'):
        positive = signature.startswith('earlyPair(')
        driver = output / (signature.split('(')[0] + '.lean')
        driver.write_text(
            'import Compiler.SolidityImport.Import\n'
            f'solidity_import probe from "{FIXTURE.parent}" entry "{FIXTURE.name}"\n'
            '  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,\n'
            '          optimizerRuns := some 800, bytecodeHash := "none" }\n'
            f'  contract {FIXTURE.stem}\n  function {signature}\n' +
            ('#guard probe.report.includedFunctions.any (fun f => f.name == "checked")\n'
             '#guard probe.report.excludedFunctions.any (fun f => f.name == "divide")\n'
             '#guard !(probe.report.includedFunctions.any (fun f => f.name == "divide"))\n'
             if positive else ''))
        result = run_bounded(['turbo-lean', '--json', 'eval', str(driver),
                              '--project-dir', '.', '--timeout-ms', '90000'])
        report = json.loads(result.stdout)
        errors = report['errors']
        if report['timed_out'] or report['crashed'] or not report['import_ok']:
            raise HarnessError(f'{signature}: incomplete elaboration: {errors}')
        if positive:
            if result.returncode or not report['ok'] or errors:
                raise HarnessError(f'{signature}: helper closure check failed: {errors}')
        elif report['ok'] or not any('solidity-import:unsupported' in msg and
                'legacy exceptional halt is not modeled' in msg and location in msg and
                'n / d' in msg.splitlines() for msg in errors):
            raise HarnessError(f'{signature}: expected rejection in the reached division: {errors}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    check_words(FIXTURE, vectors(), args.output, args.prepared)
    check_reachable_helpers(args.output.resolve())
