"""Legacy bytes pointers versus solc and an independent physical-byte memory oracle.

Pointer arithmetic wraps; a pointer assignment performs no memory access. Read
cases stay inside a finite memory domain. Gas/resource exhaustion is excluded.
"""
import argparse
from pathlib import Path
import random
import sys

from eth_abi import encode
from eth_utils import keccak
from .check_legacy_signature_calls import campaign, validator_expectation, SENDER

MOD = 1 << 256
FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyBytePointers.sol')
DRIVER = FIXTURE.with_name('LegacyBytePointersModel.lean')


def ok(*values):
    return 'ok', '0x' + encode(['uint256'] * len(values), [x % MOD for x in values]).hex()


def fail(message):
    return 'revert', '0x' + (keccak(text='Error(string)')[:4] + encode(['string'], [message])).hex()


class Memory:
    """Independent byte-addressed layout of the legacy ABI-v1 decoder."""
    def __init__(self, buffers):
        self.bytes = bytearray(8192)
        self.headers = []
        free = 128
        self.bytes[64:96] = free.to_bytes(32, 'big')
        for data in buffers:
            self.headers.append(free)
            self.bytes[free:free+32] = len(data).to_bytes(32, 'big')
            self.bytes[free+32:free+32+len(data)] = data
            self.bytes[free+32+len(data):free+64+len(data)] = bytes(32)
            free += 32 + (len(data)+31)//32*32
            self.bytes[64:96] = free.to_bytes(32, 'big')

    def load(self, address):
        address %= MOD
        if address + 32 > len(self.bytes):
            raise ValueError('test memory address outside independent finite domain')
        return int.from_bytes(self.bytes[address:address+32], 'big')


def transactions(seed, caller, accounts, random_cases):
    rng = random.Random(seed)
    calls, expected = [], {}

    def add(signature, values, outcome):
        types = signature[signature.index('(')+1:-1].split(',')
        raw = encode(types, values)
        ident = str(len(calls))
        calls.append({'id': ident, 'function': signature.split('(')[0],
            'args': [int.from_bytes(raw[i:i+32], 'big') for i in range(0,len(raw),32)],
            'sender': SENDER, 'target': caller, 'value': '0x0',
            'data': '0x'+keccak(text=signature)[:4].hex()+raw.hex(),
            'timestamp': 1000000100+len(calls), 'blockNumber': len(accounts)+2+len(calls)})
        expected[ident] = outcome

    for target in (0, 1, 64, 96, 128, MOD-1, MOD-32, 1<<255):
        add('empty(uint256)', [target], ok(96,0,128))
        add('lazy(uint256)', [target], ok(target))
    lengths = [0,1,31,32,33,65,129] + [rng.randrange(200) for _ in range(random_cases)]
    for length in lengths:
        data = rng.randbytes(length)
        other = rng.randbytes(70)
        memory, pair = Memory([data]), Memory([data,other])
        add('zero(bytes)', [data], ok(0))
        add('live(bytes)', [data], ok(0,7,0))
        offsets = [0,1,31,32,33,65,129,256,MOD-1,MOD-128]
        for offset in offsets:
            header = (160+offset)%MOD
            add('inspect(bytes,uint256)', [data,offset],
                ok(header,memory.load(header),memory.load(header+32)))
            add('root(bytes,uint256)', [data,offset],
                ok(memory.load(128+offset),length))
            add('helper(bytes,uint256)', [data,offset], ok(memory.load(header),length))
            for take in (False,True):
                chosen = (pair.headers[1]+32+offset)%MOD if take else pair.headers[1]
                add('choose(bytes,bytes,uint256,bool)', [data,other,offset,take],
                    ok(pair.load(chosen),length,length))
        for count in (0,1,2,3,4):
            add('loop(bytes,uint256,uint256)', [data,0,count],
                fail('count') if count>3 else ok(memory.load(96 if count==0 else 160+(count-1)*32)))
    # Solidity writes selector/hash/offset before reading the aliased header.
    # A forward copy can then read a word written by its preceding iteration.
    for offset in (4,36,68,100):
        for h in (0,1,4):
            memory = Memory([])
            p = 128
            def store(address, value):
                memory.bytes[address:address+32] = value.to_bytes(32, 'big')
            selector = int.from_bytes(keccak(text='validate(bytes32,bytes)')[:4], 'big')
            store(p, selector << 224)
            store(p+4, h)
            store(p+36, 64)
            size = memory.load(p+offset)
            store(p+68, size)
            for i in range(0, size, 32):
                store(p+100+i, memory.load(p+offset+32+i))
            payload = bytes(memory.bytes[p+100:p+100+size])
            for target in (accounts[0], accounts[3], accounts[11]):
                add('overlap(address,bytes32,uint256)', [target,h.to_bytes(32,'big'),offset],
                    validator_expectation(target,h.to_bytes(32,'big'),payload,'word',True,accounts))
    # Complete, unaligned, truncated, oversized, and wrapping sub-buffer headers.
    buffers = []
    for offset in (0,1,31,32,33,65):
        for length in (0,1,31,32,33,65):
            body = rng.randbytes(length)
            buffers.append((rng.randbytes(offset)+length.to_bytes(32,'big')+body+b'after',offset))
    buffers += [(b'',0),(b'x'*31,0),(bytes(32),1),((100).to_bytes(32,'big')+b'x',0),
                ((MOD-1).to_bytes(32,'big'),0),(bytes(64),MOD-31),(bytes(64),MOD-1)]
    targets = [accounts[0],accounts[3],accounts[5],accounts[7],accounts[10],accounts[11],
               '0x'+'00'*19+'02',SENDER]
    for data,offset in buffers:
        for target in targets:
            h = rng.randbytes(32)
            start = (offset+32)%MOD
            if start<offset: outcome=fail('overflow')
            elif start>len(data): outcome=fail('header')
            else:
                length=int.from_bytes(data[offset:start],'big')
                finish=(start+length)%MOD
                if finish<start: outcome=fail('overflow')
                elif finish>len(data): outcome=fail('payload')
                else: outcome=validator_expectation(target,h,data[start:finish],'word',True,accounts)
            add('validate(address,bytes32,bytes,uint256)',[target,h,data,offset],outcome)
    rows=[{'args':[str(h),'0','0','0'],'output':[]} for h in (7,11)]
    return calls,rows,expected


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--context',type=int,choices=(0,1,2),default=0)
    parser.add_argument('--optimized',action='store_true')
    parser.add_argument('--random-cases',type=int,default=4)
    args=parser.parse_args()
    if args.random_cases<0: parser.error('random-cases must be nonnegative')
    return campaign(args.output, context=args.context, optimized=args.optimized,
        random_cases=args.random_cases, fixture=FIXTURE, driver_template=DRIVER,
        make_transactions=transactions)


if __name__=='__main__':
    sys.exit(main())
