"""Independent old-value, write-once and rollback expectations for helper arguments."""
import argparse
from pathlib import Path
import random
from eth_abi import encode
from eth_utils import keccak
from .check_legacy_state_transitions import campaign, word, error, event, SENDER
from .check_legacy_scalar_conditionals import decode

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyPostIncrementArguments.sol')
FUNCTIONS = ('set(uint256)', 'last(uint256,bool,bool)', 'first(uint256,bool)',
    'middle(uint256,bool)', 'discard(uint256)', 'pair(uint256)', 'nested(uint256)',
    'forward(bytes)', 'digest(bytes,uint256)', 'copy(bytes)', 'localCounter(uint256,uint256)', 'narrow(uint8,uint256)',
    'aliases(uint256)')
MOD = 1 << 256
MASK = MOD - 1


def scenario(kind, caller, layout, **_):
    rng = random.Random(7627)
    slots = {f['label']: int(f['slot']) for f in layout['storage']}
    current = {slot: 0xC001+slot for slot in slots.values()}
    current[slots['count']] = MASK
    current[9999] = 0xABCDE
    initial = [(caller, word(slot), word(value)) for slot, value in sorted(current.items())]
    calls, expected = [], {}

    def add(signature, values=(), *, raw=None, label=''):
        types = signature[signature.index('(')+1:-1].split(',')
        if raw is None:
            raw = encode(types, values)
        name = signature.split('(')[0]
        ident = str(len(calls))
        calls.append(dict(id=ident, label=label or name, function=name,
            args=[int.from_bytes(raw[i:i+32].ljust(32, b'\0'), 'big')
                  for i in range(0, len(raw), 32)], sender=SENDER, target=caller, value='0x0',
            data='0x'+(keccak(text=signature)[:4]+raw).hex(),
            timestamp=1000000100+len(calls), blockNumber=2+len(calls)))
        v = decode(raw, types)
        status, data, logs = 'revert', '0x', []
        if v is not None:
            next_state = current.copy()
            slot = slots['count']
            old = current[slot]
            result, reason = [], None
            if name == 'set':
                next_state[slot] = v[0]
            elif name in ('localCounter', 'narrow', 'aliases'):
                a = v[0]
                b = a if name == 'aliases' else v[1]
                width = 256 if name == 'narrow' else MOD
                result = [(a+b) % MOD, (a+1) % width]
            else:
                next_state[slot] = (old+1) % MOD
                tag = len(v[0]) if name in ('forward', 'copy', 'digest') else v[0]
                if name == 'digest':
                    digest = keccak(encode(['uint256']*4, [old, next_state[slot], v[1], tag]))
                    result = [int.from_bytes(digest, 'big')]
                elif name == 'pair':
                    result = [(old+tag) % MOD, next_state[slot]]
                else:
                    logs.append(event(caller, 'Observed(uint256,uint256,uint256)',
                        ['uint256']*3, [tag, old, next_state[slot]]))
                    result = [old]
                    if name in ('last', 'first', 'middle') and v[1]:
                        reason = 'helper'
                    elif name == 'last' and v[2]:
                        reason = 'outer'
                    elif name == 'discard':
                        result = []
                    elif name == 'copy':
                        result.append(160 + 32*((tag+31)//32))
                    elif name == 'nested':
                        result = [next_state[slot]]
                        next_state[slot] = (old+2) % MOD
                        logs.append(event(caller, 'Observed(uint256,uint256,uint256)',
                            ['uint256']*3, [tag, result[0], next_state[slot]]))
            if reason is not None:
                status, data, logs = 'revert', error(reason), []
            else:
                current.update(next_state)
                status, data = 'ok', '0x'+encode(['uint256']*len(result), result).hex()
        expected[ident] = dict(status=status, data=data, events=logs,
            storage=[[caller, word(slot), word(value)] for slot, value in sorted(current.items())])

    values = (0, 1, 254, 255, 256, (1 << 128)-1, MASK-1, MASK)
    for n in values:
        for name in ('last', 'first', 'middle', 'discard', 'pair', 'nested'):
            signature = next(s for s in FUNCTIONS if s.startswith(name+'('))
            for fail in (False, True) if name in ('last', 'first', 'middle') else (False,):
                add('set(uint256)', [n])
                v = [MASK-n]
                if name in ('last', 'first', 'middle'):
                    v.append(fail)
                if name == 'last':
                    v.append(fail)
                add(signature, v)
                # A later successful call observes whether the preceding call rolled back.
                add('pair(uint256)', [7])
        add('set(uint256)', [n])
        add('last(uint256,bool,bool)', [11, False, True])
        add('pair(uint256)', [13])
        for tag in (0, 1, MASK):
            add('localCounter(uint256,uint256)', [n, tag])
            add('narrow(uint8,uint256)', raw=n.to_bytes(32,'big')+tag.to_bytes(32,'big'))
        add('aliases(uint256)', [n])
    for name in ('forward', 'copy', 'digest'):
        for n in (0, MASK-1, MASK):
            for size in (0, 1, 31, 32, 33, 65):
                add('set(uint256)', [n])
                signature = 'digest(bytes,uint256)' if name == 'digest' else name+'(bytes)'
                args = [rng.randbytes(size)] + ([MASK-n] if name == 'digest' else [])
                add(signature, args)
    for signature in FUNCTIONS:
        name = signature.split('(')[0]
        types = signature[signature.index('(')+1:-1].split(',')
        raw = (encode(types, [b'\xA5'*33]+([17] if name == 'digest' else [])) if 'bytes' in types
               else b''.join(MASK.to_bytes(32,'big') for _ in types))
        for end in (0, 1, 31, 32*len(types)-1):
            add(signature, raw=raw[:end], label='truncated')
        add(signature, raw=raw+b'\xFF'*17, label='dirty-and-trailing')
        if 'bytes' in types:
            for malformed in (word(32)[2:]+word(MASK)[2:], word(MASK)[2:]):
                add(signature, raw=bytes.fromhex(malformed), label='bad-dynamic-bounds')
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--context', type=int, choices=(0,1,2), default=0)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--prepared', action='store_true')
    return campaign(**vars(parser.parse_args()), fixture=FIXTURE,
        contract='LegacyPostIncrementArguments', functions=FUNCTIONS, scenario_builder=scenario)


if __name__ == '__main__':
    raise SystemExit(main())
