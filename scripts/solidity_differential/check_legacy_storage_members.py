"""Exact packed-word expectations for legacy direct storage-struct members."""
import argparse
import json
import random
from pathlib import Path
from eth_utils import keccak
from .engine import HarnessError, write_json
from .check_legacy_state_transitions import campaign, word, error, event, SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyStorageMembers.sol')
FUNCTIONS = ('read()', 'setPayload(uint160)', 'setCounter(uint16)', 'setMarker(uint8)',
    'setFlag(bool)', 'setOwner(address)', 'setDigest(bytes32)', 'setWide(uint256)',
    'setTiny(uint8)', 'setEnabled(bool)', 'increment(uint16)', 'guarded(uint16,bool)',
    'failAfterWrite(uint8)')
READ_FIELDS = ('primary.payload','primary.counter','primary.marker','primary.flag',
    'values.owner','values.digest','values.wide','values.tiny','values.enabled','secondary.counter')
SETTERS = dict(zip(FUNCTIONS[1:10], ('primary.payload','primary.counter','primary.marker',
    'primary.flag','values.owner','values.digest','values.wide','values.tiny','values.enabled')))
MASK = (1 << 256) - 1


def scenario(kind, caller, layout, **_):
    # Independently decode solc's physical offsets. Never read the imported model.
    fields = {}
    end = 0
    for item in layout['storage']:
        ty = layout['types'][item['type']]
        slot = int(item['slot'])
        end = max(end, slot + (int(ty['numberOfBytes'])+31)//32)
        for member in ty.get('members', []):
            mt = layout['types'][member['type']]
            fields[item['label']+'.'+member['label']] = (
                slot+int(member['slot']), 8*int(member['offset']),
                8*int(mt['numberOfBytes']), mt['label']=='bool')
    rng = random.Random(7623)
    state = {slot:rng.getrandbits(256) for slot in range(end)}
    state[9999] = 0xABCDE
    def read(name):
        slot,shift,width,boolean = fields[name]
        result = (state[slot] >> shift) & ((1<<width)-1)
        return int(result != 0) if boolean else result
    def write(name, value, *, clean=True):
        slot,shift,width,boolean = fields[name]
        if boolean and clean:
            value = int(value != 0)
        mask = ((1<<width)-1)<<shift
        state[slot] = (state[slot] & (MASK^mask)) | ((value<<shift)&mask)
    write('primary.signedCanary',0x800001)
    write('primary.flag',2,clean=False)
    write('values.enabled',128,clean=False)
    write('primary.counter',65535)
    write('secondary.counter',0xBEEF)
    initial = [(caller,word(slot),word(value)) for slot,value in sorted(state.items())]
    calls,expected = [],{}
    def add(signature, args):
        nonlocal state
        before = dict(state)
        values = []
        logs = []
        failure = None
        if signature == 'read()':
            values = [read(f) for f in READ_FIELDS]
        elif signature in SETTERS:
            write(SETTERS[signature],args[0])
        elif signature == 'increment(uint16)':
            write('primary.counter',read('primary.counter')+(args[0]&65535))
        elif signature == 'guarded(uint16,bool)':
            if not read('primary.flag'):
                failure = 'closed'
            else:
                write('primary.flag',0)
                write('primary.counter',read('primary.counter')+(args[0]&65535))
                values = [read('primary.counter')]
                logs = [event(caller,'Edited(uint16)',['uint16'],values)]
                if args[1]:
                    failure = 'after'
                else:
                    write('primary.flag',1)
        else:
            assert signature == 'failAfterWrite(uint8)'
            value = args[0]&255
            write('primary.marker',value)
            logs = [event(caller,'Tagged(uint8)',['uint8'],[value])]
            if value == 13:
                failure = 'blocked'
        if failure:
            state,logs = before,[]
        ident = str(len(calls))
        raw = b''.join(value.to_bytes(32,'big') for value in args)
        calls.append(dict(id=ident,label=signature,function=signature.split('(')[0],args=args,
            sender=SENDER,target=caller,value='0x0',data='0x'+(keccak(text=signature)[:4]+raw).hex(),
            timestamp=1000000100+len(calls),blockNumber=2+len(calls)))
        expected[ident] = {'status':'revert' if failure else 'ok',
            'data':error(failure) if failure else '0x'+''.join(word(v)[2:] for v in values),
            'events':logs,'storage':[[caller,word(slot),word(value)] for slot,value in sorted(state.items())]}
    def step(signature,args):
        add(signature,args)
        add('read()',[])
    add('read()',[])
    for n,reject in [(1,0),(0,0),(2,1),(0,1),(65535,256),(MASK,0)]:
        step('guarded(uint16,bool)',[n,reject])
    for n in [0,1,13,255,256,65535,MASK] + [rng.getrandbits(256) for _ in range(4)]:
        for signature in SETTERS:
            step(signature,[n])
        step('increment(uint16)',[n])
        step('failAfterWrite(uint8)',[n])
        step('guarded(uint16,bool)',[n,0])
    return initial,calls,expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--optimized',action='store_true')
    parser.add_argument('--mutation',choices=['neighbor-clobber','missing-restore'])
    args = parser.parse_args()
    out = args.output.resolve()
    fixture = FIXTURE
    if args.mutation:
        fixture = out.with_suffix('.sol')
        if fixture.exists():
            raise HarnessError('mutation source already exists')
        marker,replacement = ('primary.flag = true;', 'primary.flag = false;') if (
            args.mutation == 'missing-restore') else (
                'primary.marker = x;', 'primary.marker = x; primary.counter = 0;')
        source = FIXTURE.read_text()
        if marker not in source:
            raise HarnessError('storage member mutation anchor missing')
        fixture.write_text(source.replace(marker,replacement,1))
    # Artifacts are built once by the caller/serial mutation setup, before identities are captured.
    result = campaign(out,kind='storage-members',contract=FIXTURE.stem,fixture=fixture,
        functions=FUNCTIONS,scenario_builder=scenario,context=2 if args.optimized else 0,
        optimized=args.optimized,prepared=True)
    report = json.loads((out/'results.json').read_text())
    if args.mutation:
        witnesses = {route:[row['id'] for row in report['expectationMismatches']
            if row['route']==route and row['field']=='storage']
            for route in ['source','model','compiled']}
        if report['divergences'] or not all(witnesses.values()):
            raise HarnessError('member defect lacks completed storage counterexamples on every route')
    elif result:
        raise HarnessError('legacy storage member observations differ')
    write_json(out/'complete.json',{'optimized':args.optimized,'mutation':args.mutation})
    print('legacy storage member checks passed' if not args.mutation else 'member mutation detected')


if __name__ == '__main__':
    main()
