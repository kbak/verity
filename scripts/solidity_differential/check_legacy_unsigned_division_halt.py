"""Check Solidity 0.7.6 unsigned zero-divisor halts and short-circuiting."""
import argparse
from pathlib import Path

from .check_legacy_word_arithmetic import WORD, check_words, products
from .engine import HarnessError, run_bounded

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyUnsignedDivisionHalt.sol')


def vectors():
    for a, b, m in products():
        yield ('wideRemainder(uint256,uint256,uint256)', (a, b, m),
               'ok' if m else 'invalid', [a * b % m] if m else [])
    for x, d in [(0, 0), (WORD - 1, 0), (0, 3), (7, 3), (WORD - 1, 1), (WORD - 1, WORD - 1)]:
        for name in ('quotient', 'remainder'):
            result = [x // d if name == 'quotient' else x % d] if d else []
            yield f'{name}(uint256,uint256)', (x, d), 'ok' if d else 'invalid', result
        a, b = x % 256, d % 256
        yield 'selected(uint8,uint8,bool)', (a, b, False), 'ok', [WORD - 1]
        yield 'selected(uint8,uint8,bool)', (a, b, True), 'ok' if b else 'invalid', [a // b] if b else []


def check_admission(output):
    template = (output / 'Driver.lean').read_text().split('  function ', 1)[0]
    for name, signature, enabled, diagnostic in [
        ('unguarded', 'quotient(uint256,uint256)', False, 'legacy exceptional halt'),
        ('binary-order', 'competingSum(uint256,uint256)', True, 'competing failures'),
        ('argument-order', 'competingModulus(uint256,uint256)', True, 'competing failures'),
    ]:
        driver = output / f'{name}.lean'
        profile = template if enabled else template.replace(', legacyDivisionHalt := true', '')
        driver.write_text(profile + '  function ' + signature + '\nend SolidityImportSmoke.LegacyStateTransitionsModel\n')
        proc = run_bounded(['lake', 'env', 'lean', driver])
        log = proc.stdout + proc.stderr
        if not proc.returncode or '[solidity-import:unsupported]' not in log or diagnostic not in log:
            raise HarnessError(f'{name} did not produce the expected located rejection: {log}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    check_words(FIXTURE, vectors(), args.output, args.prepared, legacy_division_halt=True)
    check_admission(args.output.resolve())
