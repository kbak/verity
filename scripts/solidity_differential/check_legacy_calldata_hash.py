"""Byte-exact calldata copying, scratch hashing, and legacy enum failure modes."""
import argparse
from pathlib import Path
import random

from eth_abi import encode
from eth_utils import keccak

from .check_legacy_state_transitions import campaign, word, SENDER, error

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyCalldataHash.sol')
FUNCTIONS = ('digest(bytes,address,uint8,bytes32,uint256)', 'copy(bytes,uint256,uint256)',
             'overlap(bytes)', 'narrow(bytes,uint8,address,bool)', 'cast(uint256)',
             'castSmall(uint8)', 'echo(uint8)', 'length(bytes)', 'integer(uint8)')
IMPORT_FUNCTIONS = (FUNCTIONS[0].replace(',uint8,', ',Mode,'), *FUNCTIONS[1:6], 'echo(Mode)', FUNCTIONS[7], 'integer(Mode)')
MOD = 1 << 256


def calldata_bytes(raw, heads):
    """ABI-v1 region validity, independent of importer expressions or emitted Yul."""
    if len(raw) < heads * 32:
        return None
    offset = int.from_bytes(raw[:32], 'big')
    if offset > 1 << 32 or offset + 32 > len(raw):
        return None
    length = int.from_bytes(raw[offset:offset+32], 'big')
    if length > 1 << 32 or offset + 32 + length > len(raw):
        return None
    return raw[offset+32:offset+32+length]


def scenario(kind, caller, layout, **_):
    rng = random.Random(7615)
    initial = {int(f['slot']): 0xC001 + int(f['slot']) for f in layout['storage']}
    initial[9999] = 0xABCDE
    rows = [(caller, word(slot), word(value)) for slot, value in sorted(initial.items())]
    calls, expected = [], {}

    def add(signature, values=(), *, raw=None, label=None):
        types = signature[signature.index('(')+1:-1].split(',')
        if raw is None:
            raw = encode(types, values)
        selector = keccak(text=signature)[:4]
        data = selector + raw
        name = signature.split('(')[0]
        ident = str(len(calls))
        calls.append(dict(id=ident, label=label or name, function=name,
            args=[int.from_bytes(raw[i:i+32].ljust(32, b'\0'), 'big') for i in range(0, len(raw), 32)],
            sender=SENDER, target=caller, value='0x0', data='0x'+data.hex(),
            timestamp=1000000100+len(calls), blockNumber=2+len(calls)))
        status, result = 'ok', b''
        words = [int.from_bytes(raw[i:i+32], 'big') for i in range(0, len(types)*32, 32)]
        payload = calldata_bytes(raw, len(types)) if types[0] == 'bytes' else b''
        if len(raw) < len(types)*32 or payload is None:
            status = 'revert'
        elif name == 'digest':
            _, account, mode, tag, count = words
            fields = encode(['bytes32', 'address', 'uint256', 'uint256', 'bytes32'],
                [tag.to_bytes(32, 'big'), (account % (1 << 160)).to_bytes(20, 'big'),
                 mode % 256, count, keccak(payload)])
            result = keccak(bytes.fromhex('abcdef') + keccak(fields))
        elif name == 'copy':
            _, source, count = words
            if count > 96:
                status, result = 'revert', bytes.fromhex(error('count')[2:])
            else:
                memory = bytearray(encode(['uint256']*4, [0x112233, 0xaabbcc, 0xddeeff, 0x778899]))
                copied = data[source:source+count]
                memory[1:1+count] = copied + bytes(count-len(copied))
                result = keccak(memory) + (128).to_bytes(32, 'big')
        elif name == 'overlap':
            memory = bytearray(max(128, len(payload)+64))
            memory[63] = 255
            memory[31:31+len(payload)] = payload
            memory[1:33] = keccak(payload)
            result = keccak(memory[1:65]) + memory[33:65]
        elif name == 'length':
            result = len(payload).to_bytes(32, 'big')
        elif name == 'narrow':
            _, small, account, flag = words
            result = keccak(encode(['uint256']*3, [small % 256, account % (1 << 160), int(flag != 0)]))
        else:
            value = words[0] if name == 'cast' else words[0] % 256
            if value >= 3:
                status = 'invalid'
            else:
                result = value.to_bytes(32, 'big')
        expected[ident] = dict(status=status, data='0x'+result.hex(), events=[],
                              storage=[list(r) for r in rows])

    for length in (0, 1, 2, 30, 31, 32, 33, 63, 64, 65, 127, 192):
        payload = rng.randbytes(length)
        for mode in range(3):
            raw = encode(['bytes', 'uint256', 'uint256', 'bytes32', 'uint256'],
                [payload, rng.getrandbits(256), mode, rng.randbytes(32), rng.getrandbits(256)])
            add(FUNCTIONS[0], raw=raw, label='dirty-address-'+str(length))
            add(FUNCTIONS[0], raw=raw+bytes.fromhex('ff')*37, label='trailing-data')
        add(FUNCTIONS[2], [payload])
        add(FUNCTIONS[7], [payload])
        for count in (0, 1, 31, 32, 33, 64, 96, 97):
            for source in (0, 4, 35, 100, 132, 132+length, 133+length, MOD-1):
                add(FUNCTIONS[1], [payload, source, count])
        raw = encode(['bytes', 'uint256', 'uint256', 'uint256'],
                     [payload, MOD-1, (1 << 200)+123, 1 << 255])
        add(FUNCTIONS[3], raw=raw, label='dirty-narrow-words')
    for n in (0, 1, 2, 3, 255, 256, 257, 258, 259, 1 << 255, MOD-1):
        for signature in (*FUNCTIONS[4:7], FUNCTIONS[8]):
            add(signature, raw=n.to_bytes(32, 'big'))
        base = encode(['bytes', 'address', 'uint256', 'bytes32', 'uint256'],
                      [b'abc', caller, n, bytes(32), 5])
        add(FUNCTIONS[0], raw=base, label='enum-entry-bound')
    for signature in (*FUNCTIONS[4:7], FUNCTIONS[8]):
        scalar = (1).to_bytes(32, 'big')
        for end in (0, 1, 31):
            add(signature, raw=scalar[:end], label='truncated-scalar-head')
        add(signature, raw=scalar+b'\xff', label='scalar-trailing-byte')
    base = encode(['bytes', 'address', 'uint8', 'bytes32', 'uint256'],
                  [bytes(range(65)), caller, 2, bytes(range(32)), 7])
    for end in (0, 1, 31, 32, 159, 160, 191, 192, 255, 256, 257, len(base)-1):
        add(FUNCTIONS[0], raw=base[:end], label='truncated-calldata')
    for offset in (0, 1, 31, 32, 128, 159, 160, 161, 192, 224, 1 << 32, (1 << 32)+1, MOD-1):
        add(FUNCTIONS[0], raw=offset.to_bytes(32, 'big')+base[32:], label='offset-bound')
    for length in (0, 1, 32, 65, 66, 96, 97, 1 << 32, (1 << 32)+1, MOD-1):
        raw = base[:160]+length.to_bytes(32, 'big')+base[192:]
        add(FUNCTIONS[0], raw=raw, label='length-bound')
    return rows, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--context', type=int, choices=(0, 1, 2), default=0)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    return campaign(**vars(args), kind='calldata-hash', fixture=FIXTURE,
                    contract='LegacyCalldataHash', functions=FUNCTIONS, scenario_builder=scenario,
                    import_functions=IMPORT_FUNCTIONS)


if __name__ == '__main__':
    raise SystemExit(main())
