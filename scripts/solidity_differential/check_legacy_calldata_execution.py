"""Forwarded calldata reaches raw CALL/DELEGATECALL through memory helpers."""
import argparse
from pathlib import Path
from .check_legacy_raw_calls import campaign, transactions

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyCalldataExecution.sol')
DRIVER = FIXTURE.with_name('LegacyCalldataExecutionModel.lean')


def calls(seed, caller, accounts, random_cases):
    rows, expected = transactions(seed, caller, accounts, random_cases, methods=('run', 'forward'))
    rows = [r for r in rows if r['function'] in ('run', 'forward')]
    return rows, {r['id']: expected[r['id']] for r in rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    args = parser.parse_args()
    return campaign(args.output, optimized=args.optimized, fixture=FIXTURE,
        driver_template=DRIVER, make_transactions=calls)


if __name__ == '__main__':
    raise SystemExit(main())
