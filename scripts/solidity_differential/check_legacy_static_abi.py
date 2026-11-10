"""Static ABI-v1 hashing versus independent ABI bytes and physical memory."""
import argparse
from pathlib import Path
import random

from eth_abi import encode
from eth_utils import keccak

from .check_legacy_byte_pointers import Memory, MOD, ok, fail
from .check_legacy_packed_hash import packed
from .check_legacy_state_transitions import campaign, word, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyStaticAbiHash.sol')
FUNCTIONS = ('digest(bytes32,uint256,address)', 'scalars(uint256,address,bool,bytes32)',
             'raw(uint8,address,bool,bytes32)', 'literals()', 'empty()', 'domain()',
             'viaHelper(bytes32)', 'inspect(bytes,bytes32,uint256)', 'mixed(bytes32,uint256)',
             'loop(bytes32,uint256)')


def encoded(memory, types, values):
    """eth_abi supplies the payload; inspect its length header and exact placement."""
    payload = encode(types, values)
    header = memory.load(64)
    memory.bytes[header:header+32] = len(payload).to_bytes(32, 'big')
    memory.bytes[header+32:header+32+len(payload)] = payload
    memory.bytes[64:96] = (header+32+len(payload)).to_bytes(32, 'big')
    return keccak(payload)


def scenario(kind, caller, layout, **_):
    rng = random.Random(7614)
    initial = {int(f['slot']): 0xC001 + int(f['slot']) for f in layout['storage']}
    initial[9999] = 0xABCDE
    rows = [(caller, word(slot), word(value)) for slot, value in sorted(initial.items())]
    calls, expected = [], {}

    def add(signature, values, outcome, *, raw=None, label=None):
        spelling = signature[signature.index('(')+1:-1]
        if raw is None:
            raw = encode(spelling.split(',') if spelling else [], values)
        ident = str(len(calls))
        calls.append({'id': ident, 'label': label or signature, 'function': signature.split('(')[0],
            'args': [int.from_bytes(raw[i:i+32], 'big') for i in range(0, len(raw), 32)],
            'sender': SENDER, 'target': caller, 'value': '0x0',
            'data': '0x'+keccak(text=signature)[:4].hex()+raw.hex(),
            'timestamp': 1000000100+len(calls), 'blockNumber': 2+len(calls)})
        expected[ident] = dict(zip(('status', 'data'), outcome), events=[], storage=[list(r) for r in rows])

    def hashed(types, values):
        return ok(int.from_bytes(keccak(encode(types, values)), 'big'))

    add('empty()', [], ok(int.from_bytes(keccak(b''), 'big'), 160))
    add('literals()', [], hashed(['uint256', 'uint256', 'bool', 'bytes4'], [0, 255, True, bytes.fromhex('12345678')]))
    add('domain()', [], hashed(['bytes32', 'uint256', 'address'], [(0x123456).to_bytes(32, 'big'), 31337, caller]))
    offsets = (0, 1, 31, 32, 33, 63, 64, 65, 66, 67, 95, 96, 97, 127, 128, 129, 160, 191, 192)
    numbers = [0, 1, MOD-1, 1 << 255, int.from_bytes(bytes(range(32)), 'big')]
    numbers += [rng.getrandbits(256) for _ in range(3)]
    for n in numbers:
        blob = n.to_bytes(32, 'big')
        account = (n % (1 << 160)).to_bytes(20, 'big')
        values = [blob, n, account]
        result = hashed(['bytes32', 'uint256', 'address'], values)
        add(FUNCTIONS[0], values, result)
        add(FUNCTIONS[0], [], ('revert', '0x'), raw=encode(['bytes32', 'uint256'], [blob, n]), label='truncated-head')
        add(FUNCTIONS[0], [], result, raw=encode(['bytes32', 'uint256', 'address'], values)+blob, label='trailing-word')
        add('viaHelper(bytes32)', [blob], hashed(['bytes32', 'uint256', 'address'], [blob, 31337, caller]))
        for flag in (False, True):
            types = ['uint8', 'uint16', 'uint96', 'uint256', 'address', 'bool',
                     'bytes1', 'bytes4', 'bytes12', 'bytes20', 'bytes32']
            vals = [n % (1 << bits) for bits in (8, 16, 96, 256)] + [account, flag]
            vals += [blob[:w] for w in (1, 4, 12, 20, 32)]
            add(FUNCTIONS[1], [n, account, flag, blob], hashed(types, vals))
        # Noncanonical ABI-v1 words must be cleaned at encoding boundaries.
        add(FUNCTIONS[2], [], hashed(['uint8', 'address', 'bool', 'bytes4'],
            [n % 256, account, n != 0, blob[:4]]), raw=blob * 4, label='dirty-scalar-words')
        for length in (0, 1, 31, 32, 33, 65):
            pad = rng.randbytes(length)
            mem = Memory([pad]); start = mem.load(64)
            digest = encoded(mem, ['uint8', 'bytes32', 'bytes4'], [7, blob, bytes.fromhex('12345678')])
            for offset in offsets:
                add('inspect(bytes,bytes32,uint256)', [pad, blob, offset],
                    ok(int.from_bytes(digest, 'big'), mem.load(64), mem.load(start+offset)))
        mem = Memory([])
        first = packed(mem, [bytes.fromhex('aabbcc'), blob])
        second = encoded(mem, ['bytes32', 'uint16'], [first, 513])
        for offset in offsets:
            add('mixed(bytes32,uint256)', [blob, offset],
                ok(int.from_bytes(second, 'big'), mem.load(64), mem.load(128+offset)))
        for count in range(6):
            current = blob
            for i in range(count): current = keccak(encode(['uint8', 'bytes32'], [i, current]))
            add('loop(bytes32,uint256)', [blob, count], fail('count') if count > 4 else
                ok(int.from_bytes(current, 'big'), 128+96*count))
    return rows, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--context', type=int, choices=(0, 1, 2), default=0)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    return campaign(**vars(args), kind='static-abi', fixture=FIXTURE, contract='LegacyStaticAbiHash',
                    functions=FUNCTIONS, scenario_builder=scenario)


if __name__ == '__main__':
    raise SystemExit(main())
