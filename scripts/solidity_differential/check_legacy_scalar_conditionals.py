"""Lazy legacy scalar conditionals against independent value/state expectations."""
import argparse
from pathlib import Path
import random
from eth_abi import encode
from eth_utils import keccak
from .check_legacy_state_transitions import campaign, word, error, event, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyScalarConditionals.sol')
CONTRACTS = {'scalar': 'LegacyScalarConditionals', 'effects': 'LegacyConditionalEffects'}
FUNCTIONS = {
    'scalar': ('choose(bool,uint256,uint256)', 'maximum(uint256,uint256)',
        'nested(bool,bool,uint256,uint256,uint256)', 'wrapped(bool,uint8,uint8)',
        'promoted(bool,uint8,uint16)', 'booleans(bool,bool,bool)',
        'addresses(bool,address,address)', 'fixedBytes(bool,bytes32,bytes32)',
        'widenedBytes(bool,bytes32,bytes32)', 'guarded(uint256,uint256)',
        'narrowGuarded(uint256,uint8)',
        'guardedNested(uint256,uint256,bool)', 'lazy(bool,uint256)',
        'negated(bool,uint256)', 'requireChoice(bool,uint256)',
        'helperArg(bool,uint256,uint256)', 'skippedCopy(bool,bytes)'),
    'effects': ('run(bool,bool)', 'increments(bool)',
        'assignments(bool,uint256,uint256)', 'failSelected(bool)'),
}
MOD = 1 << 256
MASK = MOD - 1


def decode(raw, types):
    """ABI-v1 scalar cleaning and dynamic bounds, without strict ABI-v2 padding."""
    if len(raw) < 32 * len(types):
        return None
    values = []
    for i, ty in enumerate(types):
        lane = raw[32*i:32*i+32]
        n = int.from_bytes(lane, 'big')
        if ty == 'bool':
            value = n != 0
        elif ty.startswith('uint'):
            value = n % (1 << int(ty[4:]))
        elif ty == 'address':
            value = '0x' + lane[-20:].hex()
        elif ty == 'bytes':
            if n > 1 << 32 or n + 32 > len(raw):
                return None
            size = int.from_bytes(raw[n:n+32], 'big')
            if size > 1 << 32 or n + 32 + size > len(raw):
                return None
            value = raw[n+32:n+32+size]
        else:
            value = lane[:int(ty[5:])]
        values.append(value)
    return values


def scalar(name, v):
    result_type = 'uint256'
    if name in ('choose', 'helperArg'):
        result = [v[1] if v[0] else v[2]]
    elif name == 'maximum':
        result = [max(v)]
    elif name == 'nested':
        result = [(v[2] if v[1] else v[3]) if v[0] else v[4]]
    elif name == 'wrapped':
        result = [(v[1]+v[2] if v[0] else v[1]-v[2]) % 256]
    elif name == 'promoted':
        result = [v[1] if v[0] else v[2]]
    elif name in ('booleans', 'addresses', 'fixedBytes', 'widenedBytes'):
        result_type = {'booleans': 'bool', 'addresses': 'address',
                       'fixedBytes': 'bytes32', 'widenedBytes': 'bytes32'}[name]
        selected = v[1] if v[0] else v[2]
        if name in ('fixedBytes', 'widenedBytes'):
            width = 1 if name == 'widenedBytes' and v[0] else 5
            selected = selected[:width].ljust(32, b'\0')
        result = [selected]
    elif name == 'guarded':
        n, d = v
        result = [n // d, n % d] if d else [0, 0]
    elif name == 'narrowGuarded':
        result = [v[0] // v[1] if v[1] else 0]
    elif name == 'guardedNested':
        n, d, flag = v
        result = [(n // d if flag else n % d) if d else 19]
    elif name in ('lazy', 'negated'):
        flag, n = v
        if flag and n == 0:
            return 'revert', error('selected')
        result = [(n+1) % MOD if flag else (7 if name == 'lazy' else 17)]
    elif name == 'requireChoice':
        flag, n = v
        if not (n > 3 if flag else n < 2):
            return 'revert', error('choice')
        result = [n]
    elif name == 'skippedCopy':
        flag, data = v
        result = [len(data), 160 + 32*((len(data)+31)//32)] if flag else [23, 128]
    else:
        raise ValueError(name)
    return 'ok', '0x' + encode([result_type]*len(result), result).hex()


def scenario(kind, caller, layout, **_):
    rng = random.Random(7624)
    slots = {f['label']: int(f['slot']) for f in layout['storage']}
    current = {slot: 0xC001+slot for slot in slots.values()}
    if kind == 'effects':
        current[slots['count']], current[slots['trace']] = MASK-1, 77
    current[9999] = 0xABCDE
    initial = [(caller, word(slot), word(value)) for slot, value in sorted(current.items())]
    calls, expected = [], {}

    def add(signature, words=None, *, raw=None, label=''):
        types = signature[signature.index('(')+1:-1].split(',')
        if raw is None:
            raw = b''.join(n.to_bytes(32, 'big') for n in words)
        name = signature.split('(')[0]
        ident = str(len(calls))
        calls.append(dict(id=ident, label=label or name, function=name,
            args=[int.from_bytes(raw[i:i+32].ljust(32, b'\0'), 'big')
                  for i in range(0, len(raw), 32)], sender=SENDER, target=caller, value='0x0',
            data='0x'+(keccak(text=signature)[:4]+raw).hex(),
            timestamp=1000000100+len(calls), blockNumber=2+len(calls)))
        v = decode(raw, types)
        status, data, logs = 'revert', '0x', []
        if v is not None and kind == 'scalar':
            status, data = scalar(name, v)
        elif v is not None:
            next_state = current.copy()
            count, trace = slots['count'], slots['trace']

            def step(tag):
                next_state[count] = (next_state[count]+1) % MOD
                next_state[trace] = tag
                logs.append(event(caller, 'Step(uint256,uint256)',
                                  ['uint256', 'uint256'], [tag, next_state[count]]))
                return next_state[count]

            reason = None
            if name == 'run':
                step(1)
                result = [step(2 if v[0] else 3)]
                reason = 'late' if v[1] else None
            elif name == 'increments':
                before = next_state[count]
                next_state[count] = (before+1) % MOD
                result = [before if v[0] else next_state[count], next_state[count]]
            elif name == 'assignments':
                selected = v[1] if v[0] else v[2]
                next_state[count] = next_state[trace] = selected
                result = [selected]
            else:
                result = [step(0 if v[0] else 4)]
                reason = 'branch' if v[0] else None
            if reason is not None:
                status, data, logs = 'revert', error(reason), []
            else:
                current.update(next_state)
                status, data = 'ok', '0x'+encode(['uint256']*len(result), result).hex()
        expected[ident] = dict(status=status, data=data, events=logs,
            storage=[[caller, word(slot), word(value)] for slot, value in sorted(current.items())])

    values = (0, 1, 2, 255, 256, 65535, 1 << 255, MASK)
    flags = (0, 1, 2, MASK)
    if kind == 'scalar':
        for flag in flags:
            for a in values:
                b = MASK-a
                for name in ('choose', 'helperArg', 'wrapped', 'promoted', 'booleans',
                             'addresses', 'fixedBytes', 'widenedBytes'):
                    signature = next(s for s in FUNCTIONS[kind] if s.startswith(name+'('))
                    add(signature, [flag, a, b])
                for name in ('lazy', 'negated', 'requireChoice'):
                    add(name+'(bool,uint256)', [flag, a])
                add('nested(bool,bool,uint256,uint256,uint256)', [flag, a, a, b, 13])
            for size in (0, 1, 31, 32, 33, 65):
                raw = bytearray(encode(['bool', 'bytes'], [bool(flag), rng.randbytes(size)]))
                raw[:32] = flag.to_bytes(32, 'big')
                add('skippedCopy(bool,bytes)', raw=bytes(raw))
        for a in values:
            for b in (0, 1, 2, 255, MASK):
                add('maximum(uint256,uint256)', [a, b])
                add('guarded(uint256,uint256)', [a, b])
                add('narrowGuarded(uint256,uint8)', [a, b])
                add('guardedNested(uint256,uint256,bool)', [a, b, rng.choice(flags)])
    else:
        for _ in range(4):
            for flag in flags:
                for fail in flags:
                    add('run(bool,bool)', [flag, fail])
                add('increments(bool)', [flag])
                add('failSelected(bool)', [flag])
                add('assignments(bool,uint256,uint256)', [flag, rng.choice(values), rng.choice(values)])
    for signature in FUNCTIONS[kind]:
        types = signature[signature.index('(')+1:-1].split(',')
        raw = (encode(['bool','bytes'], [True,b'\xA5'*33]) if 'bytes' in types
               else b''.join((1 if ty=='bool' else MASK).to_bytes(32,'big') for ty in types))
        for end in (0, 1, 31, 32*len(types)-1):
            add(signature, raw=raw[:end], label='truncated')
        add(signature, raw=raw+b'\xFF'*17, label='trailing-bytes')
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--kind', choices=CONTRACTS, default='scalar')
    parser.add_argument('--context', type=int, choices=(0,1,2), default=0)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--prepared', action='store_true')
    args = vars(parser.parse_args())
    kind = args['kind']
    return campaign(**args, fixture=FIXTURE, contract=CONTRACTS[kind],
                    functions=FUNCTIONS[kind], scenario_builder=scenario)


if __name__ == '__main__':
    raise SystemExit(main())
