"""Independent raw-word expectations for immutable legacy scalar forwarding."""
import argparse
from pathlib import Path
import random
from eth_abi import encode
from eth_utils import keccak
from .check_legacy_state_transitions import campaign, word, error, event, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyHelperAssemblyScalars.sol')
FUNCTIONS = ('set(uint256)', 'direct(address,uint8,uint8,bool)', 'nested(address,uint8)',
    'pair(address,uint8)', 'payableAddress(address)', 'repeated(address,address)',
    'checkedEnum(uint8)', 'record(address,uint8,bool)', 'digest(address,uint8,bool)')
IMPORTS = ('set(uint256)', 'direct(address,Mode,uint8,bool)', 'nested(address,Mode)',
    'pair(address,Mode)', 'payableAddress(«address payable»)', 'repeated(address,address)',
    'checkedEnum(Mode)', 'record(address,Mode,bool)', 'digest(address,Mode,bool)')
MOD = 1 << 256
MASK = MOD - 1
ADDRESS_MASK = (1 << 160) - 1


def scenario(kind, caller, layout, **_):
    slots = {f['label']: int(f['slot']) for f in layout['storage']}
    current = {slot: 0xC001 + slot for slot in slots.values()}
    current[slots['count']] = MASK
    current[9999] = 0xABCDE
    initial = [(caller, word(slot), word(value)) for slot, value in sorted(current.items())]
    calls, expected = [], {}

    def add(signature, values=(), *, raw=None, label=''):
        types = signature[signature.index('(')+1:-1].split(',')
        if raw is None:
            raw = b''.join(n.to_bytes(32, 'big') for n in values)
        name = signature.split('(')[0]
        ident = str(len(calls))
        calls.append(dict(id=ident, label=label or name, function=name,
            args=[int.from_bytes(raw[i:i+32].ljust(32, b'\0'), 'big')
                  for i in range(0, len(raw), 32)], sender=SENDER, target=caller, value='0x0',
            data='0x'+(keccak(text=signature)[:4]+raw).hex(),
            timestamp=1000000100+len(calls), blockNumber=2+len(calls)))
        status, data, logs = 'revert', '0x', []
        if len(raw) >= 32*len(types):
            values = [int.from_bytes(raw[32*i:32*i+32], 'big') for i in range(len(types))]
            # ABI-v1 cleans widths, including enum uint8, without checking enum membership.
            v = [n & ADDRESS_MASK if ty == 'address' else n & 255 if ty == 'uint8'
                 else int(n != 0) if ty == 'bool' else n for ty, n in zip(types, values)]
            result = v.copy()
            status = 'ok'
            if name == 'set':
                current[slots['count']] = v[0]
                result = []
            elif name == 'checkedEnum':
                if v[0] >= 3:
                    status = 'invalid'
                result = [v[0], v[0]]
            elif name in ('record', 'digest'):
                old = current[slots['count']]
                if v[2]:
                    status, data = 'revert', error('outer')
                else:
                    current[slots['count']] = (old+1) % MOD
                    if name == 'record':
                        logs = [event(caller, 'Observed(uint256,uint256,uint256)',
                            ['uint256']*3, [v[0], v[1], old])]
                        result = []
                    else:
                        result = [int.from_bytes(keccak(encode(['uint256']*3,
                            [v[0], v[1], old])), 'big')]
            if status == 'ok':
                data = '0x'+encode(['uint256']*len(result), result).hex()
        expected[ident] = dict(status=status, data=data, events=logs,
            storage=[[caller, word(slot), word(value)] for slot, value in sorted(current.items())])

    values = (0, 1, 2, 3, 254, 255, 256, 257, ADDRESS_MASK,
              1 << 160, (1 << 200)+7, MASK)
    for n in values:
        add('direct(address,uint8,uint8,bool)', [n, n, n, n])
        add('nested(address,uint8)', [n, n])
        add('pair(address,uint8)', [n, n])
        add('payableAddress(address)', [n])
        add('repeated(address,address)', [n, MASK-n])
        add('checkedEnum(uint8)', [n])
        for old in (0, MASK):
            for name in ('record', 'digest'):
                for fail in (0, 1, 256):
                    add('set(uint256)', [old])
                    add(name+'(address,uint8,bool)', [n, n, fail])
                    # The next hash independently exposes rollback or a missing/double increment.
                    add('digest(address,uint8,bool)', [17, 255, 0])
    rng = random.Random(7633)
    for _ in range(24):
        add('direct(address,uint8,uint8,bool)', [rng.getrandbits(256) for _ in range(4)])
    for signature in FUNCTIONS:
        size = len(signature[signature.index('(')+1:-1].split(','))
        raw = b'\xFF' * (32*size)
        for end in sorted({0, 1, 31, 32*size-1}):
            add(signature, raw=raw[:end], label='truncated')
        add(signature, raw=raw+b'\xA5'*17, label='dirty-and-trailing')
    return initial, calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--context', type=int, choices=(0, 1, 2), default=0)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--prepared', action='store_true')
    return campaign(**vars(parser.parse_args()), fixture=FIXTURE,
        contract='LegacyHelperAssemblyScalars', functions=FUNCTIONS,
        import_functions=IMPORTS, scenario_builder=scenario)


if __name__ == '__main__':
    raise SystemExit(main())
