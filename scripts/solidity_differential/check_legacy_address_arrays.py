"""ABI-v1 address arrays: exact decoding, cleanup, helper reads and atomic writes.

Expected results come from an independent byte decoder and list requirements,
not the imported model. Unsupported exceptional halts remain rejection controls.
"""
import argparse
from pathlib import Path
import random

from eth_abi import encode
from eth_utils import keccak

from .check_legacy_state_transitions import campaign, error, event, word, MASK
from .check_interface_word_static_call import SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyAddressArrays.sol')
FUNCTIONS = ('initializeList(address[],uint256)', 'fold(address[],address[])')
ADDRESS_MASK = (1 << 160) - 1


def words(values):
    return b''.join(n.to_bytes(32, 'big') for n in values)


def array(values):
    return words([len(values), *values])


def payload(first, second, *, fold=False):
    if fold:
        return words([64, 96 + 32 * len(first)]) + array(first) + array(second)
    return words([64, second]) + array(first)


def decode(data, *, fold=False):
    """The pinned v1 ABI accepts overlapping/unaligned tails and dirty addresses."""
    if len(data) < 64:
        return None
    read = lambda offset: int.from_bytes(data[offset:offset + 32], 'big')
    arrays = []
    for head in (0, 32) if fold else (0,):
        offset = read(head)
        if offset > 2**32 or offset + 32 > len(data):
            return None
        length = read(offset)
        if length > 2**32 or offset + 32 + 32 * length > len(data):
            return None
        arrays.append([read(offset + 32 + 32 * i) & ADDRESS_MASK for i in range(length)])
    return (arrays[0], arrays[1] if fold else read(32))


def inputs(caller, seed=7612):
    for requested in (0, 1, MASK):
        yield f'empty-{requested}', 0, payload([], requested)
    for items, reason in (([0], 'zero'), ([1], 'sentinel'), ([int(caller, 16)], 'self'),
                          ([11, 11], 'adjacent'), ([11, 12, 11], 'duplicate'),
                          ([11, 12, 0], 'late-zero'), ([11, 12, 1], 'late-sentinel')):
        yield reason, 0, payload(items, 1)
    yield 'upper-bound', 0, payload([11, 12], 3)
    yield 'zero-threshold', 0, payload([11, 12], 0)
    for data in (b'', words([64]), words([64, 1]), words([64, 1, 1]),
                 words([64, 1, 2, 11]), words([2**32, 1, 0]), words([2**32 + 1, 1, 0]),
                 words([MASK, 1, 0]), words([64, 1, 2**32]), words([64, 1, 2**32 + 1]),
                 words([64, 1, MASK])):
        yield 'malformed-init', 0, data
    for first, second in (([], []), ([11], []), ([], [12]), ([11, 12], [13, 14]),
                           ([MASK, 1 << 160, (1 << 200) + 20], [ADDRESS_MASK])):
        yield 'fold', 1, payload(first, second, fold=True)
    # Independent tails, shared tails, head/tail overlap, and unaligned headers.
    yield 'shared-tail', 1, words([64, 64, 2, (1 << 200) + 25, 26])
    yield 'head-overlap', 1, words([0, 64, 0])
    unaligned = words([65, 65]) + b'\xff' + array([(1 << 240) + 27])
    yield 'unaligned', 1, unaligned.ljust((len(unaligned) + 31) // 32 * 32, b'\xff')
    for head in (0, 1):
        for bad in (2**32, 2**32 + 1, MASK):
            data = bytearray(payload([11], [12], fold=True))
            data[32*head:32*(head+1)] = words([bad])
            yield 'malformed-fold', 1, bytes(data)
    rng = random.Random(seed)
    for _ in range(12):
        first = [rng.getrandbits(256) for _ in range(rng.randrange(6))]
        second = [rng.getrandbits(256) for _ in range(rng.randrange(6))]
        yield 'random-fold', 1, payload(first, second, fold=True)
    yield 'dirty-initialize', 0, payload([(1 << 200) + 21, (1 << 160) + 22, 23], 2)
    yield 'reinitialize', 0, payload([31, 32], 1)
    yield 'reinitialize-error-order', 0, payload([0], 0)
    yield 'decode-before-body', 0, words([MASK, 0])


def scenario(_kind, caller, layout, *, functions=None, fields=None, errors=None,
             dirty_mappings=False, emit_items=True, include_fold=True, **_):
    functions = functions or FUNCTIONS
    fields = fields or ('links', 'count', 'limit')
    errors = errors or dict(initialized='initialized', bound='bound', zero='zero',
                            key='key', duplicate='duplicate')
    slots = {f['label']: int(f['slot']) for f in layout['storage']}
    mapping = lambda key: int.from_bytes(keccak(encode(['uint256', 'uint256'],
                                                 [key, slots[fields[0]]])), 'big')
    calls = [row for row in inputs(caller) if include_fold or row[1] == 0]
    keys = {0, 1, int(caller, 16)}
    for _, index, data in calls:
        decoded = decode(data, fold=index == 1)
        if index == 0 and decoded:
            keys.update(decoded[0])
    current = {int(f['slot']): 0 for f in layout['storage']}
    current[9999] = 0xABCDE
    current.update({mapping(key): (0xABCDE << 160 if dirty_mappings else 0) for key in keys})
    initial = [(caller, word(slot), word(value)) for slot, value in sorted(current.items())]
    transactions, expected = [], {}
    for label, index, data in calls:
        signature = functions[index]
        ident = str(len(transactions))
        transactions.append({'id': ident, 'label': label, 'function': signature.split('(')[0],
            'args': [int.from_bytes(data[i:i+32], 'big') for i in range(0, len(data), 32)],
            'sender': SENDER, 'target': caller, 'value': '0x0',
            'data': '0x' + (keccak(text=signature)[:4] + data).hex(),
            'timestamp': 1000000100 + len(transactions), 'blockNumber': 2 + len(transactions)})
        decoded = decode(data, fold=index == 1)
        after, logs, reason, output = dict(current), [], None, '0x'
        if decoded is None:
            reason = ''
        elif index == 1:
            output = word(sum(decoded[0] + decoded[1]) & MASK)
        else:
            items, requested = decoded
            if current[slots[fields[2]]] != 0:
                reason = errors['initialized']
            elif requested > len(items):
                reason = errors['bound']
            elif not requested:
                reason = errors['zero']
            else:
                # Validate the list as a whole before committing the required links.
                # Adjacent duplicates fail the key guard; other repeats fail membership.
                previous, seen = 1, set()
                for item in items:
                    if item in (0, 1, int(caller, 16), previous):
                        reason = errors['key']
                        break
                    if item in seen or (current[mapping(item)] & ADDRESS_MASK):
                        reason = errors['duplicate']
                        break
                    seen.add(item)
                    previous = item
                if reason is None:
                    for before, after_key in zip([1] + items, items + [1]):
                        slot = mapping(before)
                        after[slot] = (after[slot] & (MASK ^ ADDRESS_MASK)) | after_key
                    after[slots[fields[1]]] = len(items)
                    after[slots[fields[2]]] = requested
                    if emit_items:
                        logs = [event(caller, 'Item(address)', ['address'], [f'0x{item:040x}'], indexed=True)
                                for item in items]
        if reason is None:
            current = after
        expected[ident] = {'status': 'revert' if reason is not None else 'ok',
            'data': error(reason) if reason else ('0x' if reason == '' else output),
            'events': [] if reason is not None else logs,
            'storage': [[caller, word(slot), word(value)] for slot, value in sorted(current.items())]}
    return initial, transactions, expected


def run(output, **kwargs):
    return campaign(output, kind='arrays', fixture=FIXTURE, contract='LegacyAddressArrays',
                    functions=FUNCTIONS, scenario_builder=scenario, **kwargs)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--context', type=int, default=0)
    parser.add_argument('--dirty-mappings', action='store_true')
    parser.add_argument('--prepared', action='store_true')
    raise SystemExit(run(**vars(parser.parse_args())))
