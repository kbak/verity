"""Legacy internal byte arguments against an independent physical-memory oracle."""
import argparse
from pathlib import Path
import random
from eth_abi import encode
from eth_utils import keccak
from .check_legacy_state_transitions import campaign, word, error, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyCalldataHelpers.sol')
FUNCTIONS = ('forward(bytes)', 'copy(bytes)', 'pair(bytes,bytes)', 'siblings(bytes)',
    'live(bytes)', 'aliasPointer(bytes)', 'dirty(bytes)', 'mixed(bytes,bytes)',
    'copyThenForward(bytes)', 'skipped(bytes,bool)', 'through(bytes)',
    'skipCopy(bytes)', 'skipForward(bytes)')
MOD = 1 << 256


class Memory:
    """Finite byte-addressed expectation, independent of the generated model."""
    def __init__(self):
        self.data = bytearray(8192)
        self.free = 128

    def load(self, p):
        if p < 0 or p + 32 > len(self.data):
            raise ValueError('memory expectation outside finite test domain')
        return int.from_bytes(self.data[p:p+32], 'big')

    def allocate(self, payload):
        p = self.free
        self.free += 32 + ((len(payload) + 31) // 32) * 32
        self.data[p:p+32] = len(payload).to_bytes(32, 'big')
        self.data[p+32:p+32+len(payload)] = payload
        self.data[p+32+len(payload):p+64+len(payload)] = bytes(32)
        return p


def decode(raw, types):
    if len(raw) < 32 * len(types):
        return None
    values = []
    for i, ty in enumerate(types):
        value = int.from_bytes(raw[i*32:(i+1)*32], 'big')
        if ty == 'bytes':
            if value > 1 << 32 or value + 32 > len(raw):
                return None
            size = int.from_bytes(raw[value:value+32], 'big')
            if size > 1 << 32 or value + 32 + size > len(raw):
                return None
            values.append(raw[value+32:value+32+size])
        else:
            values.append(value != 0)
    return values


def outcome(name, values):
    m = Memory()
    data = values[0]
    if name == 'dirty':
        if len(data) > 96:
            return 'revert', error('size')
        m.data[128:384] = b'\xff' * 256
    if name in ('copy', 'through', 'dirty'):
        p = m.allocate(data)
        result = [p, len(data), m.free, m.load(p+32), m.load(p+32+len(data)),
                  m.load(m.free+32)]
    elif name in ('forward', 'copyThenForward'):
        if name == 'copyThenForward':
            m.allocate(data)
        result = [len(data), int.from_bytes(keccak(data), 'big'), m.free]
    elif name == 'pair':
        a, b = m.allocate(data), m.allocate(values[1])
        result = [a, b, len(data), len(values[1]), m.free]
    elif name == 'mixed':
        a = m.allocate(data)  # The memory root is decoded before the body.
        b = m.allocate(values[1])
        result = [a, b, a, len(values[1]), m.free]
    elif name == 'siblings':
        result = [m.allocate(data), m.allocate(data), m.free]
    elif name == 'live':
        before = m.load(m.free)
        p = m.allocate(data)
        result = [before, m.load(p), p]
    elif name == 'aliasPointer':
        p = m.allocate(data)
        result = [len(data), m.load(p+32), p]
    elif name in ('skipCopy', 'skipForward'):
        if name == 'skipCopy':
            m.allocate(data)
        result = [m.free]
    elif name == 'skipped':
        if values[1]:
            m.allocate(data)
        result = [m.free]
    else:
        raise ValueError(name)
    return 'ok', '0x' + encode(['uint256'] * len(result), result).hex()


def scenario(kind, caller, layout, **_):
    rng = random.Random(7623)
    rows = [(caller, word(int(f['slot'])), word(0xC001 + int(f['slot'])))
            for f in layout['storage']]
    rows.append((caller, word(9999), word(0xABCDE)))
    calls, expected = [], {}

    def add(signature, values=(), *, raw=None, label=''):
        types = signature[signature.index('(')+1:-1].split(',')
        raw = encode(types, values) if raw is None else raw
        name = signature.split('(')[0]
        ident = str(len(calls))
        calls.append(dict(id=ident, label=label or name, function=name,
            args=[int.from_bytes(raw[i:i+32].ljust(32, b'\0'), 'big')
                  for i in range(0, len(raw), 32)], sender=SENDER, target=caller, value='0x0',
            data='0x'+(keccak(text=signature)[:4]+raw).hex(),
            timestamp=1000000100+len(calls), blockNumber=2+len(calls)))
        decoded = decode(raw, types)
        status, data = ('revert', '0x') if decoded is None else outcome(name, decoded)
        expected[ident] = dict(status=status, data=data, events=[], storage=[list(r) for r in rows])

    lengths = (0, 1, 2, 30, 31, 32, 33, 63, 64, 65, 95, 96, 97, 127, 192)
    for length in lengths:
        payload = rng.randbytes(length)
        for signature in FUNCTIONS:
            if signature.endswith('(bytes)'):
                add(signature, [payload])
                raw = bytearray(encode(['bytes'], [payload]))
                raw[64+length:] = b'\xff' * (len(raw)-64-length)
                add(signature, raw=bytes(raw)+b'\xa5'*37, label='dirty-padding')
        other = rng.randbytes(lengths[(length+5) % len(lengths)])
        for signature in ('pair(bytes,bytes)', 'mixed(bytes,bytes)'):
            add(signature, [payload, other])
            raw = encode(['bytes', 'bytes'], [payload, other])
            add(signature, raw=raw[:32]+raw[:32]+raw[64:], label='shared-calldata-offset')
        for flag in (0, 1, MOD-1):
            add('skipped(bytes,bool)', raw=encode(['bytes', 'uint256'], [payload, flag]))
    for signature in FUNCTIONS:
        types = signature[signature.index('(')+1:-1].split(',')
        values = [rng.randbytes(65) if ty == 'bytes' else True for ty in types]
        raw = encode(types, values)
        for end in (0, 1, 31, 32*len(types)-1, len(raw)-32, len(raw)-1):
            add(signature, raw=raw[:end], label='truncated')
        for offset in (0, 1, 31, 32, 33, 1 << 32, (1 << 32)+1, MOD-1):
            add(signature, raw=offset.to_bytes(32, 'big')+raw[32:], label='offset-boundary')
        offset = int.from_bytes(raw[:32], 'big')
        for size in (0, 1, 64, 65, 66, 96, 97, 1 << 32, (1 << 32)+1, MOD-1):
            changed = raw[:offset] + size.to_bytes(32, 'big') + raw[offset+32:]
            add(signature, raw=changed, label='length-boundary')
    return rows, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--context', type=int, choices=(0, 1, 2), default=0)
    parser.add_argument('--prepared', action='store_true')
    return campaign(**vars(parser.parse_args()), kind='calldata-helpers', fixture=FIXTURE,
        contract='LegacyCalldataHelpers', functions=FUNCTIONS, scenario_builder=scenario)


if __name__ == '__main__':
    raise SystemExit(main())
