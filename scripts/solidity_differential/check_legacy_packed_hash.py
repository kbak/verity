"""Legacy static packed hashing, including its observable physical memory writes."""
import argparse
from pathlib import Path
import random
import sys

from eth_abi import encode
from eth_keys import keys
from eth_keys.constants import SECPK1_N
from eth_utils import keccak
from .check_legacy_byte_pointers import Memory, MOD, fail, ok
from .check_legacy_signature_calls import BACKEND, SENDER, campaign, recovery

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyPackedHash.sol')
DRIVER = FIXTURE.with_name('LegacyPackedHashModel.lean')
PREFIX = b'Typed digest:\n32'


def packed(memory, parts):
    """Independent legacy encoder: overlapping 32-byte writes, unrounded allocation."""
    header = memory.load(64)
    cursor = header + 32
    for part in parts:
        for index in range(0, len(part), 32):
            word = part[index:index+32].ljust(32, b'\0')
            memory.bytes[cursor+index:cursor+index+32] = word
        cursor += len(part)
    payload = bytes(memory.bytes[header+32:cursor])
    memory.bytes[header:header+32] = len(payload).to_bytes(32, 'big')
    memory.bytes[64:96] = cursor.to_bytes(32, 'big')
    return keccak(payload)


def transactions(seed, caller, accounts, random_cases):
    rng = random.Random(seed)
    calls, rows, expected = [], {}, {}

    def add(signature, values, outcome):
        spelling = signature[signature.index('(')+1:-1]
        raw = encode(spelling.split(',') if spelling else [], values)
        ident = str(len(calls))
        calls.append({'id': ident, 'function': signature.split('(')[0],
            'args': [int.from_bytes(raw[i:i+32], 'big') for i in range(0, len(raw), 32)],
            'sender': SENDER, 'target': caller, 'value': '0x0',
            'data': '0x'+keccak(text=signature)[:4].hex()+raw.hex(),
            'timestamp': 1000000100+len(calls), 'blockNumber': len(accounts)+2+len(calls)})
        expected[ident] = outcome

    def number(blob):
        return int.from_bytes(blob, 'big')

    add('empty()', [], ok(number(keccak(b'')), 160))
    values = [0, 1, MOD-1, 1 << 255, int.from_bytes(bytes(range(32)), 'big')]
    values += [rng.getrandbits(256) for _ in range(random_cases)]
    offsets = [0, 1, 31, 32, 33, 34, 35, 63, 64, 65, 66, 67, 68, 69, 70, 95, 96, 97, 128, 160]
    for n in values:
        word = n.to_bytes(32, 'big')
        add('digest(bytes32)', [word], ok(number(keccak(PREFIX+word))))
        literal = b'\xce\xbb\0'+word+bytes(range(33))+b'\xff'*32+b'\0'
        add('literals(bytes32)', [word], ok(number(keccak(literal))))
        for flag in (False, True):
            account = (n % (1 << 160)).to_bytes(20, 'big')
            payload = b''.join((n % (1 << (8*w))).to_bytes(w, 'big') for w in (1, 2, 12, 32))
            payload += account + bytes([flag]) + b''.join(word[:w] for w in (1, 4, 12, 20, 32))
            add('scalars(uint256,address,bool,bytes32)', [n, account, flag, word],
                ok(number(keccak(payload))))
        for length in (0, 1, 31, 32, 33, 65):
            pad = rng.randbytes(length)
            mem = Memory([pad]); start = mem.load(64)
            digest = packed(mem, [b'\1\2\3', word, b'\2\1'])
            for offset in offsets:
                add('inspect(bytes,bytes32,uint256)', [pad, word, offset],
                    ok(number(digest), mem.load(64), mem.load(start+offset)))
        mem = Memory([])
        first = packed(mem, [b'\xaa\xbb\xcc', word])
        second = packed(mem, [first, b'\xdd'])
        for offset in offsets:
            add('chain(bytes32,uint256)', [word, offset],
                ok(number(second), mem.load(64), mem.load(128+offset)))
        for count in range(6):
            current = word
            for i in range(count): current = keccak(bytes([i])+current)
            add('loop(bytes32,uint256)', [word, count],
                fail('count') if count > 4 else ok(number(current), 128+65*count))
        # Invalid recovery leaves its scratch arguments above the new free pointer.
        mem = Memory([])
        mem.bytes[128:160] = bytes(32)
        mem.bytes[160:288] = word+bytes(32)+word+word
        mem.bytes[64:96] = (160).to_bytes(32, 'big')
        digest = packed(mem, [b'\xab'])
        rows[(n, 0, n, n)] = []
        for offset in offsets:
            add('scratch(bytes32,uint256)', [word, offset],
                ok(number(digest), mem.load(64), mem.load(160+offset)))
        hashed = keccak(PREFIX+word)
        key = keys.PrivateKey((7).to_bytes(32, 'big'), backend=BACKEND)
        sig = key.sign_msg_hash(hashed)
        for v, r, s in [(sig.v+27, sig.r, sig.s), (28-sig.v, sig.r, SECPK1_N-sig.s),
                        (sig.v+283, sig.r, sig.s), (0, sig.r, sig.s), (27, 0, sig.s)]:
            result = recovery(hashed, v % 256, r, s)
            rows[(number(hashed), v % 256, r, s)] = result
            add('recover(bytes32,uint256,bytes32,bytes32)',
                [word, v, r.to_bytes(32, 'big'), s.to_bytes(32, 'big')], ok(result[0] if result else 0))
    return calls, [{'args': list(map(str, args)), 'output': list(map(str, out))}
                   for args, out in rows.items()], expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--context', type=int, choices=(0, 1, 2), default=0)
    parser.add_argument('--random-cases', type=int, default=4)
    args = parser.parse_args()
    return campaign(args.output, optimized=args.optimized, context=args.context,
        random_cases=args.random_cases, fixture=FIXTURE, driver_template=DRIVER,
        make_transactions=transactions)


if __name__ == '__main__':
    sys.exit(main())
