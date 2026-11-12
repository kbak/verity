"""Independent checked-add expectations for protected assignment siblings."""
import argparse
import json
import random
from pathlib import Path
from eth_utils import keccak
from .engine import HarnessError, write_json
from .check_legacy_state_transitions import campaign, word, error, event, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyAssignmentSiblings.sol')
FUNCTIONS = ('add(uint256,uint256)', 'rightSide(uint256,uint256)', 'nested(uint256,uint256)',
    'modified(uint256,uint256)', 'skipped(uint256,uint256,bool)', 'shadowed(uint256,uint256)',
    'narrow(uint8,uint8)', 'record(uint256,uint256)')
MASK = (1 << 256) - 1


def scenario(kind, caller, layout, **_):
    slots = {row['label']:int(row['slot']) for row in layout['storage']}
    state = {slot: 0xC001+slot for slot in slots.values()}
    state[slots['count']] = 7
    state[9999] = 0xABCDE
    initial = [(caller,word(slot),word(value)) for slot,value in sorted(state.items())]
    calls, expected = [], {}
    def add(signature, values):
        name = signature.split('(')[0]
        x, y = values[:2]
        if name == 'modified':
            x = (x+1) & MASK
        if name == 'narrow':
            x, y = x & 255, y & 255
        result, fail = (x+y) & MASK, x+y > MASK
        if name == 'narrow':
            result, fail = (x+y) & 255, x+y > 255
        elif name == 'shadowed':
            result, fail = (x+y+1) & MASK, y == MASK or x+y+1 > MASK
        elif name == 'skipped' and not values[2]:
            result, fail = 17, False
        logs = []
        if not fail and name == 'record':
            logs = [event(caller,'Assigned(uint256)',['uint256'],[(state[slots['count']]+1)&MASK]),
                    event(caller,'Assigned(uint256)',['uint256'],[result])]
            state[slots['count']] = result
        raw = b''.join(n.to_bytes(32,'big') for n in values)
        ident = str(len(calls))
        calls.append(dict(id=ident,label=name,function=name,args=values,sender=SENDER,
            target=caller,value='0x0',data='0x'+(keccak(text=signature)[:4]+raw).hex(),
            timestamp=1000000100+len(calls),blockNumber=2+len(calls)))
        expected[ident] = {'status':'revert' if fail else 'ok',
            'data':error('narrow') if fail and name == 'narrow' else '0x' if fail else word(result),
            'events':logs, 'storage':[[caller,word(slot),word(value)] for slot,value in sorted(state.items())]}
    pairs = [(0,0),(1,0),(0,MASK),(MASK,0),(MASK,1),(MASK-1,1),(MASK-1,2),
             (1<<255,1<<255),((1<<128)-1,1<<128),(255,1),(128,127)]
    rng = random.Random(7639)
    pairs += [(rng.getrandbits(256),rng.getrandbits(256)) for _ in range(8)]
    for x,y in pairs:
        for signature in FUNCTIONS:
            if signature.startswith('skipped('):
                for enabled in (0,1,256):
                    add(signature,[x,y,enabled])
            else:
                add(signature,[x,y])
    return initial,calls,expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--optimized',action='store_true')
    parser.add_argument('--prepared',action='store_true')
    parser.add_argument('--mutation',choices=['drop-guard','drop-assignment'])
    args = parser.parse_args()
    out = args.output.resolve()
    fixture = FIXTURE
    if args.mutation:
        # Keep the requirement oracle unchanged; only the candidate source changes.
        out.parent.mkdir(parents=True,exist_ok=True)
        fixture = out.with_suffix('.sol')
        if fixture.exists():
            raise HarnessError('mutation source already exists')
        replacement = 'z = x + y;' if args.mutation == 'drop-guard' else 'require(x + y >= x);'
        source = FIXTURE.read_text()
        marker = 'require((z = x + y) >= x);'
        if marker not in source:
            raise HarnessError('assignment mutation anchor missing')
        fixture.write_text(source.replace(marker,replacement,1))
    result = campaign(out,kind='assignment-siblings',contract=FIXTURE.stem,fixture=fixture,
        functions=FUNCTIONS,scenario_builder=scenario,context=2 if args.optimized else 0,
        optimized=args.optimized,prepared=args.prepared)
    report = json.loads((out/'results.json').read_text())
    if args.mutation:
        # Compilation errors are exceptions; divergence is never a mutation kill.
        rows = report['expectationMismatches']
        wanted_field = 'status' if args.mutation == 'drop-guard' else 'data'
        witnesses = {route:[row['id'] for row in rows
            if row['route']==route and row['field']==wanted_field and row['label']=='add']
            for route in ['source','model','compiled']}
        if report['divergences'] or not all(witnesses.values()):
            raise HarnessError('assignment defect lacks completed counterexamples on every route')
    elif result:
        raise HarnessError('assignment sibling observations differ')
    write_json(out/'complete.json',{'optimized':args.optimized,'mutation':args.mutation})
    print('assignment sibling checks passed' if not args.mutation else 'assignment mutation detected')


if __name__ == '__main__':
    main()
