"""Exact ordered event bytes through loops, helpers, modifier returns and rollback."""
import argparse
from pathlib import Path

from eth_abi import encode
from eth_utils import keccak

from .check_observed_storage import check


def event(signature, indexed=(), data=()):
    def payload(values):
        return encode([ty for ty, _ in values], [value for _, value in values])
    return dict(address='$self', topics=['0x'+keccak(text=signature).hex()] +
                ['0x'+payload([value]).hex() for value in indexed],
                data='0x'+payload(data).hex())


def cases():
    rows = []

    def add(signature, args, returned, total, logs, reason=None):
        types = signature.split('(', 1)[1][:-1].split(',')
        encoded = encode(types, args)
        result = (keccak(text='Error(string)')[:4]+encode(['string'], [reason])
                  if reason else encode(['uint256']*len(returned), returned))
        rows.append(dict(id=str(len(rows)), function=signature.split('(')[0], signature=signature,
            words=[str(int.from_bytes(encoded[i:i+32], 'big')) for i in range(0, len(encoded), 32)],
            calldata='0x'+(keccak(text=signature)[:4]+encoded).hex(),
            slots=['0', '9'], initial=['7', '12345'],
            expected=dict(status='revert' if reason else 'ok', data='0x'+result.hex(),
                storage=[str(7 if reason else total), '12345'], events=[] if reason else logs)))

    stage = lambda value: event('Stage(uint8)', data=[('uint8', value)])
    for n, stop in [(0, 0), (1, 0), (4, 0), (4, 1), (4, 2), (4, 3)]:
        end = stop if 1 <= stop <= n else n
        for fail_at, fail_after in [(0, False), (2, False), (0, True)]:
            total = 7
            logs = [stage(1)]
            for index in range(1, end+1):
                total += index
                logs.append(event('Step(uint16,uint256)', [('uint16', index)],
                                  [('uint256', total)]))
                if index != 2:
                    logs.append(event('Empty()'))
                if index == stop:
                    break
                if index != 2:
                    logs.append(stage(2))
            logs.append(stage(3))
            reason = 'body' if 1 <= fail_at <= end else 'post' if fail_after else None
            add('walk(uint256,uint256,uint256,bool)', [n, stop, fail_at, fail_after],
                [total], total, logs, reason)
    # An independent fixed topic address distinguishes payload addresses from the emitter.
    for small, signed, tag, flag in [(0, 0, b'\0'*4, False),
                                    (65535, -(2**23), bytes.fromhex('deadbeef'), True),
                                    (257, 2**23-1, bytes.fromhex('01020304'), False)]:
        logs = [event('Typed(address,bytes4,bool,uint16,bytes1)',
                      [('address', '0x0000000000000000000000000000000000005678'),
                       ('bytes4', tag), ('bool', flag)], [('uint16', small), ('bytes1', b'\xab')]),
                event('Signed(int24,int24)', [('int24', signed)], [('int24', signed)]),
                event('Empty()')]
        add('typed(uint16,int24,bytes4,bool)', [small, signed, tag, flag], [], 7, logs)
    return rows


SPEC = dict(
    fixture=Path('Contracts/SolidityImportSmoke/LegacyObservedEvents.sol'),
    contract='LegacyObservedEvents', cases=cases, layout=[('total', '0', 0)],
    helpers=['traced', 'helper'], excluded=['hidden'],
    negatives=[('hidden()', 'anonymous events are unsupported')],
    bounded_rejection='Solidity 0.7.6 while loops require an unsigned local compared with zero',
)


def run(output, optimized=False):
    check(output, optimized=optimized, ordinary_import=True, spec=SPEC)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    run(**vars(parser.parse_args()))
