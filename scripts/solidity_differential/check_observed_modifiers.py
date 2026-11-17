"""Source modifier ordering, early returns and rollback through observed imports."""
import argparse
from pathlib import Path

from eth_abi import encode
from eth_utils import keccak

from .check_observed_storage import check


def cases():
    rows = []
    initial = [7, 0, 0]

    def add(signature, args, returned, state, reason=None):
        types = signature.split('(', 1)[1][:-1].split(',')
        encoded = encode(types, args)
        data = (keccak(text='Error(string)')[:4] + encode(['string'], [reason])
                if reason else encode(['uint256'] * len(returned), returned))
        rows.append(dict(id=str(len(rows)), function=signature.split('(')[0], signature=signature,
            words=[str(int.from_bytes(encoded[i:i+32], 'big')) for i in range(0, len(encoded), 32)],
            calldata='0x' + (keccak(text=signature)[:4] + encoded).hex(),
            slots=['0', '1', '2', '9'], initial=list(map(str, initial + [12345])),
            expected=dict(status='revert' if reason else 'ok', data='0x'+data.hex(),
                storage=list(map(str, (initial if reason else state) + [12345])))))

    for n, stop in [(0, 0), (1, 0), (4, 0), (4, 1), (4, 2), (4, 3)]:
        end = stop if 1 <= stop <= n else n
        total = 7 + end * (end + 1) // 2
        stamp = 12
        for i in range(1, end + 1):
            if i == stop:
                break
            if i != 2:
                stamp = stamp * 10 + 3
        stamp = stamp * 100 + 76
        for before, after in [(False, False), (True, False), (False, True)]:
            add('walk(uint256,uint256,bool,bool)', [n, stop, before, after], [total],
                [total + 100, stamp, 0], 'pre' if before else 'post' if after else None)
    for n in (0, 1, 4):
        add('tuple(uint256)', [n], [9, 4] if n else [4, 9], [7, 16, 0])
        add('snapshot(uint256)', [n], [7 + n], [17 + n, 7, 0])
        add('voidLoop(uint256)', [n], [], [7 + min(n, 2) + (10 if n < 2 else 0), 16, 0])
        add('failBody(uint256)', [n], [n], [107 + n, 0, 0], 'body' if n >= 2 else None)
    for n, stop in [(0, 0), (4, 0), (4, 1), (4, 2)]:
        end = stop if 1 <= stop <= n else n
        for fail in (False, True):
            add('through(uint256,uint256,bool)', [n, stop, fail], [7 + end],
                [1107 + end, 164, 0], 'post' if fail else None)
    return rows


SPEC = dict(
    fixture=Path('Contracts/SolidityImportSmoke/LegacyObservedModifiers.sol'),
    contract='LegacyObservedModifiers', cases=cases,
    layout=[('total', '0', 0), ('stamp', '1', 0), ('locked', '2', 0)],
    helpers=['marked', 'guarded', 'captured', 'checked', 'check', 'helper'],
    excluded=['skipped', 'twice', 'ambiguous'],
    bounded_rejection='Solidity 0.7.6 while loops require an unsigned local compared with zero',
    negatives=[('skipped(bool)', 'require an unconditional body placeholder'),
               ('twice()', 'only a single top-level _; placeholder'),
               ('ambiguous()', 'observed tuple return requires unambiguous scalar components')],
)


def run(output, optimized=False):
    check(output, optimized=optimized, ordinary_import=True, spec=SPEC)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    run(**vars(parser.parse_args()))
