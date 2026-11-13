"""Legacy signed scalars: integer oracle, exact ABI/reverts, three execution routes.

The oracle computes with unbounded Python integers. ABI words are encoded manually
so dirty sign bits and truncated heads exercise original solc decoding as well.
"""
import argparse
import json
from pathlib import Path
import random

from eth_utils import keccak
from .engine import HarnessError, write_json
from .check_legacy_state_transitions import campaign, word, error, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacySignedScalars.sol')
WIDTHS = (8, 24, 128, 256)
MODULUS = 1 << 256
FUNCTIONS = [
    'applyDelta(uint128,int128)', 'checkedUnsigned(uint256)',
    'checkedNarrow(int256)', 'checkedSign(uint256)', 'signedCasts(int256)',
    'unsignedCasts(uint256)', 'widen(int8,uint8)', 'literals()', 'defaultLocal()',
    'explicitAbi(int8,bytes)',
] + [f'{op}{bits}(int{bits},int{bits})' for bits in WIDTHS for op in ('arithmetic', 'compare')]


def signed(value, bits):
    value %= 1 << bits
    return value if value < 1 << (bits - 1) else value - (1 << bits)


def scenario(kind, caller, layout, **_):
    strict = kind == 'signed-v2'
    initial = [[caller, word(int(f['slot'])), word(0xBEEF)] for f in layout['storage']]
    initial += [[caller, word(9999), word(0xC0FFEE)]]
    calls, expected = [], {}

    def add(signature, values, *, truncated=False):
        name, types = signature.split('(', 1)
        types = types[:-1].split(',') if types != ')' else []
        words = [value % MODULUS for value in values]
        raw = b''.join(value.to_bytes(32, 'big') for value in words)
        if name == 'explicitAbi':
            raw += (64).to_bytes(32, 'big') + bytes(32)
        if truncated:
            raw = raw[:-1]
        reason, result = None, []
        decoded = []
        for typ, value in zip(types, words):
            bits = int(typ.removeprefix('uint').removeprefix('int'))
            decoded.append(signed(value, bits) if typ.startswith('int') else value % (1 << bits))
            if strict and value != decoded[-1] % MODULUS:
                reason = ''
        if truncated:
            reason = ''
        if reason is None:
            if name == 'applyDelta':
                x, y = decoded
                result = [x + y]
                if result[0] < 0:
                    reason = 'decrease'
                elif result[0] >= 1 << 128:
                    reason = 'increase'
            elif name == 'checkedUnsigned':
                result = decoded
                if decoded[0] >= 1 << 160:
                    reason = ''
            elif name == 'checkedNarrow':
                result = decoded
                if not -(1 << 127) <= decoded[0] < 1 << 127:
                    reason = ''
            elif name == 'checkedSign':
                result = decoded
                if decoded[0] >= 1 << 255:
                    reason = ''
            elif name == 'signedCasts':
                x = decoded[0]
                result = [signed(x, n) for n in (8, 24, 128)] + [x % (1 << 16), x % MODULUS]
            elif name == 'unsignedCasts':
                result = [signed(decoded[0], n) for n in WIDTHS]
            elif name == 'widen':
                x, y = decoded
                result = [x, x % (1 << 16), y]
            elif name == 'literals':
                result = [(1 << 128) - 1, 128, -1, 0, 1, 127]
            elif name == 'defaultLocal':
                result = [0]
            elif name == 'explicitAbi':
                result = decoded
            elif name.startswith('arithmetic'):
                bits, x, y = int(name.removeprefix('arithmetic')), *decoded
                result = [signed(n, bits) for n in (x+y, x-y, x*y, -x)]
            elif name.startswith('compare'):
                x, y = decoded
                result = [int(v) for v in (x<y, x<=y, x>y, x>=y, x==y, x!=y)]
            else:
                raise HarnessError(f'unhandled oracle function {name}')
        ident = str(len(calls))
        payload_words = [int.from_bytes(raw[i:i+32].ljust(32, b'\0'), 'big')
            for i in range(0, len(raw), 32)]
        calls.append(dict(id=ident, label=name, function=name, args=payload_words, sender=SENDER,
            target=caller, value='0x0', data='0x'+(keccak(text=signature)[:4]+raw).hex(),
            timestamp=1000000100+len(calls), blockNumber=2+len(calls)))
        expected[ident] = dict(status='ok' if reason is None else 'revert',
            data=('0x'+''.join(word(n % MODULUS)[2:] for n in result)) if reason is None
                else error(reason) if reason else '0x', events=[], storage=initial)

    rng = random.Random(760128)
    for bits in WIDTHS:
        half = 1 << (bits-1)
        pairs = [(0,0), (1,-1), (-1,1), (half-1,1), (-half,-1), (-half,-half),
                 (half-1,half-1), (-half,half-1), (-1,-1), (half,1), (MODULUS-1,1)]
        pairs += [(rng.getrandbits(256), rng.getrandbits(256)) for _ in range(4)]
        for op in ('arithmetic','compare'):
            signature = f'{op}{bits}(int{bits},int{bits})'
            for values in pairs:
                add(signature, values)
            add(signature, [0,0], truncated=True)
    values = [0,1,127,128,255,256,-1,-128,-129,1<<23,-(1<<23),
        (1<<127)-1,1<<127,-(1<<127),-(1<<127)-1,(1<<128)-1,1<<128,
        (1<<160)-1,1<<160,(1<<255)-1,1<<255,MODULUS-1]
    values += [rng.getrandbits(256) for _ in range(6)]
    for signature in FUNCTIONS[1:6]:
        for x in values:
            add(signature, [x])
        add(signature,[0],truncated=True)
    for x,y in [(0,0),(0,-1),(1,-1),(0,1),(1<<127,-(1<<127)),
        ((1<<127)-1,-(1<<127)),((1<<128)-1,1),((1<<128)-1,0),
        ((1<<128)-1,-1),(0,-(1<<127)),((1<<128)-1,(1<<127)-1),
        (1<<128,0),(7,(1<<200)-1),(MODULUS-1,MODULUS-1)]:
        add(FUNCTIONS[0],[x,y])
    for x,y in [(0,0),(-1,255),(128,128),(127,256),(MODULUS-1,MODULUS-1)]:
        add('widen(int8,uint8)',[x,y])
    for x in (0,127,128,255,256,MODULUS-1):
        add('explicitAbi(int8,bytes)',[x])
    add('literals()',[])
    add('defaultLocal()',[])
    return initial,calls,expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--optimized',action='store_true')
    parser.add_argument('--prepared',action='store_true')
    parser.add_argument('--abi-v2',action='store_true')
    parser.add_argument('--context',type=int,choices=(0,1,2),default=0)
    parser.add_argument('--mutation',choices=('drop-cast-guard','drop-delta-guard'))
    args = parser.parse_args()
    out, fixture = args.output.resolve(), FIXTURE
    if args.mutation or args.abi_v2:
        out.parent.mkdir(parents=True,exist_ok=True)
        fixture = out.with_suffix('.sol')
        if fixture.exists():
            raise HarnessError('candidate source already exists')
        source = FIXTURE.read_text()
        if args.abi_v2:
            # Legacy dynamic memory allocation remains v1-only; test scalar v2 roots.
            source = source.replace('pragma solidity 0.7.6;',
                'pragma solidity 0.7.6; pragma abicoder v2;')
        if args.mutation:
            marker, replacement = {
                'drop-cast-guard': ('require((z = int128(y)) == y);', 'z = int128(y);'),
                'drop-delta-guard': ('require((z = x - uint128(-y)) < x, "decrease");',
                                     'z = x - uint128(-y);'),
            }[args.mutation]
            if source.count(marker) != 1:
                raise HarnessError('signed mutation anchor missing')
            source = source.replace(marker,replacement)
        fixture.write_text(source)
    functions = [f for f in FUNCTIONS if not (args.abi_v2 and f.startswith('explicitAbi'))]
    def selected_scenario(*a, **kw):
        initial, calls, expected = scenario(*a, **kw)
        if args.abi_v2:
            calls = [tx for tx in calls if tx['function'] != 'explicitAbi']
            expected = {tx['id']:expected[tx['id']] for tx in calls}
        return initial,calls,expected
    result = campaign(out,kind='signed-v2' if args.abi_v2 else 'signed-v1',
        contract=FIXTURE.stem,fixture=fixture,functions=functions,scenario_builder=selected_scenario,
        context=args.context,optimized=args.optimized,prepared=args.prepared)
    report = json.loads((out/'results.json').read_text())
    if args.mutation:
        label = 'checkedNarrow' if args.mutation == 'drop-cast-guard' else 'applyDelta'
        witnesses = {route:[row['id'] for row in report['expectationMismatches']
            if row['route']==route and row['field']=='status' and row['label']==label]
            for route in ('source','model','compiled')}
        if report['divergences'] or not all(witnesses.values()):
            raise HarnessError('signed mutation lacks completed counterexamples on every route')
    elif result:
        raise HarnessError('signed scalar observations differ from the integer oracle')
    write_json(out/'complete.json',dict(optimized=args.optimized,abi_v2=args.abi_v2,
        context=args.context,mutation=args.mutation))
    print('signed scalar checks passed' if not args.mutation else 'signed mutation detected')


if __name__ == '__main__':
    main()
