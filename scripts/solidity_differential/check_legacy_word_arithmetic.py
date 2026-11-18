"""Compare legacy Yul word arithmetic with arbitrary-precision integer results."""
import argparse
from pathlib import Path

from eth_abi import encode
from eth_utils import keccak

from .check_legacy_state_transitions import SENDER, campaign
from .engine import HarnessError

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyWordArithmetic.sol')
WORD = 1 << 256


def check_words(fixture, vectors, output, prepared, **options):
    rows = list(vectors)

    def scenario(kind, caller, layout, **_):
        calls, expected = [], {}
        for signature, args, status, values in rows:
            name, types = signature[:-1].split('(')
            raw = encode(types.split(','), args)
            ident = str(len(calls))
            calls.append(dict(id=ident, label=name, function=name, target=caller, sender=SENDER,
                              value='0x0', blockNumber=2 + len(calls), timestamp=1000000100 + len(calls),
                              data='0x' + (keccak(text=signature)[:4] + raw).hex(),
                              args=[int.from_bytes(raw[i:i+32], 'big') for i in range(0, len(raw), 32)]))
            data = encode(['uint256'] * len(values), [v % WORD for v in values])
            expected[ident] = dict(status=status, data='0x' + data.hex(), events=[], storage=[])
        return [], calls, expected

    if campaign(output, kind=fixture.stem, contract=fixture.stem, fixture=fixture,
                functions=list(dict.fromkeys(row[0] for row in rows)), scenario_builder=scenario,
                optimized=True, optimizer_runs=800, prepared=prepared, **options):
        raise HarnessError(f'{fixture.stem} differs from integer or halt expectations')


def products():
    return [(0, 0, 0), (7, 3, 0), (6, 3, 5), (7, 3, 5), (1 << 200, 1 << 100, 97),
            (WORD - 1, WORD - 2, WORD - 3), (WORD - 1, 0, WORD - 1)]


def vectors():
    for a, b, m in products():
        yield 'assemblyWords(uint256,uint256,uint256)', (a, b, m), 'ok', [
            a * b % m if m else 0, -(-a // b) if b else 0, int(a + b >= WORD)]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    check_words(FIXTURE, vectors(), args.output, args.prepared)
