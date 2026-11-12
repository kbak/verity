"""Independent physical-slot/state specification; never reads imported models or solc layout."""
import copy

from keccak256 import keccak_256, selector
from .check_packed_memory_hash import CONCRETE_HASH, packed_preimage, vectors, word
from .engine import HarnessError
from .stateful import ROUTES, validate_observation

PACKED_ARCHIVE_SHA256 = '2fc836a2b785b6a4871053899c8f46c48788d6d475445fd0ca6cb946e19c1196'
BASE_SLOT = 2  # outerBefore at 0, Bucket at 1, its mapping member at relative slot 1.
COUNT_MASK = 2**128 - 1
SLOT_ANCHORS = {
    2: '647774934d1d39c0e89e35d63775c7d2ad06bd10443d86a92dd3f721d3142979',
    3: 'b77511b1cce69066467ebe61941cbc4aa6defec0a694e9405cf32401a0fc13b0',
}
KEY_TYPES = 'address,int24,int24,bytes32'
SIGNATURES = {
    name: f'{name}({KEY_TYPES}{suffix})' for name, suffix in (
        ('read', ''), ('setCount', ',uint128'), ('setAccumulator', ',uint256'),
        ('setCheckpoint', ',uint256'), ('writeThenRevert', ',uint128'))
}
EVENT = '0x' + keccak_256(b'Changed(uint8,uint256)').hex()


def hexword(n):
    return '0x' + word(n).hex()


def record_slot(key, mapping_base):
    """Solidity bytes32 mapping addressing, including the explicit enclosing offset."""
    return int.from_bytes(keccak_256(bytes.fromhex(key) + word(mapping_base)), 'big')


def specification(target, sender, layout_shift=0):
    """Fixed input sequence with explicit storage, return bytes, logs and rollback at every step."""
    if layout_shift not in (0, 1):
        raise HarnessError('unsupported fixture layout shift')
    base = BASE_SLOT + layout_shift
    if hexword(record_slot(CONCRETE_HASH, base))[2:] != SLOT_ANCHORS[base]:
        raise HarnessError('independent mapping-slot anchor changed')
    packed = [{'values': list(map(str, v)), 'preimage': packed_preimage(*v).hex(),
               'hash': keccak_256(packed_preimage(*v)).hex()} for v in vectors()]
    # Keep all packed expectations archived; these six distinct keys cover the state matrix.
    indices = (0, 1, 25, 37, 52, 53)
    keys = [packed[i] for i in indices]
    slots = [record_slot(k['hash'], base) for k in keys]
    if len(set(slots)) != len(slots):
        raise HarnessError('fixture keys unexpectedly alias')
    # Physical slot zero through four cover both outer and struct-relative sentinels.
    state = {i: 0xa000 + i for i in range(5 + layout_shift)}
    for index, slot in enumerate(slots):
        for offset in (-1, 0, 1, 2, 3):
            physical = (slot + offset) % 2**256
            if physical in state:
                raise HarnessError('independent fixture slot overlap')
            state[physical] = (0xb000 + index * 8 + offset if offset in (-1, 3) else 0)
        # Seed only the first three records; preserve high uint128 padding on updates.
        if index < 3:
            state[slot] = ((0xcafe + index) << 128) + 11 + index
            state[(slot + 1) % 2**256] = 101 + index
            state[(slot + 2) % 2**256] = 201 + index
    initial = dict(state)
    calls = [('read', i, None) for i in range(6)]
    calls += [
        ('setCount', 0, COUNT_MASK), ('setAccumulator', 1, 2**256 - 1),
        ('setCheckpoint', 0, 2**255), ('setCount', 0, 0),
        ('writeThenRevert', 0, 123), ('read', 0, None), ('read', 1, None),
        ('setCount', 3, 7), ('setAccumulator', 3, 99), ('setCheckpoint', 3, 100),
        ('writeThenRevert', 4, COUNT_MASK), ('read', 4, None),
        ('setCount', 1, 42), ('setAccumulator', 0, 1), ('setCheckpoint', 1, 0),
        ('setCount', 0, COUNT_MASK), ('writeThenRevert', 1, 0),
    ]
    calls += [('read', i, None) for i in range(6)]
    transactions, expected = [], []
    for index, (operation, key_index, next_word) in enumerate(calls):
        key, slot = keys[key_index], slots[key_index]
        arguments = list(map(int, key['values'])) + ([] if next_word is None else [next_word])
        signature = SIGNATURES[operation]
        ident = f'{index}:{operation}:{key_index}'
        transactions.append({'id': ident, 'function': operation,
            'args': [n % 2**256 for n in arguments], 'sender': sender, 'target': target,
            'data': selector(signature) + b''.join(word(n) for n in arguments).hex(),
            'value': '0x0', 'timestamp': 1000000100 + index, 'blockNumber': 2 + index})
        events, status = [], 'ok'
        if operation == 'writeThenRevert':
            # No successful state or logs survive, even for a previously absent record.
            status, data = 'revert', selector('Rejected(uint128)') + word(next_word).hex()
        else:
            if operation != 'read':
                field = {'setCount': 0, 'setAccumulator': 1, 'setCheckpoint': 2}[operation]
                at = (slot + field) % 2**256
                state[at] = ((state[at] & ~COUNT_MASK) | next_word if field == 0 else next_word)
                events = [{'address': target, 'topics': [EVENT, hexword(field)],
                           'data': hexword(next_word)}]
            values = [state[slot] & COUNT_MASK, state[(slot + 1) % 2**256],
                      state[(slot + 2) % 2**256]]
            data = '0x' + b''.join(word(n) for n in values).hex()
        expected.append({'id': ident, 'status': status, 'data': data, 'events': events,
                         'storage': [[target, hexword(k), hexword(v)] for k, v in sorted(state.items())]})
    return {'mappingBase': base, 'packedExpectations': packed, 'keyIndices': list(indices),
            'recordSlots': [hexword(s) for s in slots], 'target': target,
            'initialStorage': [[target, hexword(k), hexword(v)] for k, v in sorted(initial.items())],
            'transactions': transactions, 'expected': expected}


def compare_expected(spec, rows):
    """Return real semantic mismatches; malformed or missing observations are infrastructure errors."""
    if len(rows) != len(spec['expected']):
        raise HarnessError('missing or extra expected-state observations')
    mismatches, cumulative = [], set()
    for want, got in zip(spec['expected'], rows):
        touched, actual = validate_observation(got)
        if got['id'] != want['id']:
            raise HarnessError('expected-state transaction identity mismatch')
        expected = {(a, s): v for a, s, v in want['storage']}
        cumulative.update(expected)
        cumulative.update(touched)
        cumulative.update(actual)
        if not cumulative <= actual.keys():
            raise HarnessError('missing sentinel or cumulative storage observation')
        fields = [k for k in ('status', 'data', 'events') if got[k] != want[k]]
        # No external calls: all unspecified physical storage, in any account, starts at zero.
        if any(actual[k] != expected.get(k, hexword(0)) for k in cumulative):
            fields.append('storage')
        if fields:
            mismatches.append({'id': want['id'], 'fields': fields})
    return mismatches


def replay_expected(spec, adapters, *, required_routes):
    """Discover every supplied route's accesses, then replay a shared cumulative plan plus sentinels.

    Source-only preparation must request exactly ('source',). Real three-route callers must
    request ROUTES; a missing model/compiled adapter can never silently reduce that requirement.
    """
    if tuple(required_routes) not in (('source',), ROUTES) or set(adapters) != set(required_routes):
        raise HarnessError('required execution routes missing or invalid')
    transactions = spec['transactions']
    fixed = [[a, s] for a, s, _ in spec['initialStorage']]

    def run(route, plan):
        rows = adapters[route](copy.deepcopy(transactions), copy.deepcopy(plan))
        if not isinstance(rows, list) or len(rows) != len(transactions):
            raise HarnessError('missing or extra expected-state observations')
        for tx, row in zip(transactions, rows):
            _, storage = validate_observation(row)
            if row['id'] != tx['id'] or not set(map(tuple, fixed)) <= storage.keys():
                raise HarnessError('missing sentinel or transaction identity mismatch')
        return copy.deepcopy(rows)

    discovery = {r: run(r, [fixed for _ in transactions]) for r in required_routes}
    plans, cumulative = [], set(map(tuple, fixed))
    for index in range(len(transactions)):
        for route in required_routes:
            touched, storage = validate_observation(discovery[route][index])
            cumulative.update(touched)
            cumulative.update(storage)
        plans.append([list(k) for k in sorted(cumulative)])
    replay = {r: run(r, plans) for r in required_routes}
    for route in required_routes:
        for index, (before, after) in enumerate(zip(discovery[route], replay[route])):
            bt, bs = validate_observation(before)
            at, observed = validate_observation(after)
            if not set(map(tuple, plans[index])) <= observed.keys():
                raise HarnessError('missing cross-route storage observation')
            if (any(before[k] != after[k] for k in ('id', 'status', 'data', 'events'))
                    or bt != at or any(observed.get(k) != v for k, v in bs.items())):
                raise HarnessError('execution changed between discovery and replay')
    return {'routes': list(required_routes), 'discovery': discovery, 'observations': replay,
            'slots': plans, 'mismatches': {r: compare_expected(spec, replay[r]) for r in required_routes}}
