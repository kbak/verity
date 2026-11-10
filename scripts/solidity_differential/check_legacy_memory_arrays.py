"""Legacy memory arrays and capacity-bounded traversal against independent requirements.

INVALID is a distinct terminal status. Oversized allocation is an empty REVERT;
resource exhaustion is an instrumentation failure, not a successful comparison.
"""
import argparse
from pathlib import Path

from eth_utils import keccak

from .check_legacy_address_arrays import ADDRESS_MASK, array, words
from .check_legacy_state_transitions import campaign, event, word, MASK
from .check_interface_word_static_call import SENDER

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyMemoryArrays.sol')
FUNCTIONS = ('allocate(uint256)', 'echo(address[])', 'read(address[],uint256)',
             'replace(address[],uint256,address)', 'sumPrefix(address[],uint256)',
             'sumOffset(address[])', 'sumExpanded(address[])', 'fill(address[])', 'enumerate()')


def encoded_array(values):
    return '0x' + (words([32]) + array(values)).hex()


def enumeration(capacity, links, sentinel=1):
    """Requirement: ordered successors, zero-filled tail, failure on excess items."""
    if capacity > (1 << 64) - 1:
        return 'revert', []
    if capacity > 256:
        raise ValueError("test oracle supports only bounded allocations or allocation overflow")
    out, current = [], links.get(sentinel, 0) & ADDRESS_MASK
    while current != sentinel:
        if len(out) == capacity:
            return 'invalid', []
        out.append(current)
        current = links.get(current, 0) & ADDRESS_MASK
    return 'ok', out + [0] * (capacity - len(out))


def cases():
    for length in (0, 1, 4, 2**64, MASK):
        yield 'allocate-' + str(length), 0, words([length]), ('revert' if length >= 2**64 else 'ok'), ([] if length >= 2**64 else [0]*length)
    for values in ([], [11], [MASK, 1 << 160, (1 << 200) + 27, 1]):
        yield 'echo', 1, words([32]) + array(values), 'ok', values
        for index in (0, len(values)-1 if values else 0, len(values), MASK):
            valid = index < len(values)
            data = words([64, index]) + array(values)
            yield 'read-' + str(index), 2, data, 'ok' if valid else 'invalid', [values[index] & ADDRESS_MASK] if valid else []
            updated = list(values)
            if valid:
                updated[index] = 35
            yield 'replace-' + str(index), 3, words([96, index, (1 << 220) + 35]) + array(values), 'ok' if valid else 'invalid', updated
        for bound in (0, len(values), len(values) + 1):
            valid = bound <= len(values)
            yield 'sum-' + str(bound), 4, words([64, bound]) + array(values), 'ok' if valid else 'invalid', [sum(n & ADDRESS_MASK for n in values[:bound]) & MASK] if valid else []
        yield 'off-by-one', 5, words([32]) + array(values), 'invalid' if values else 'ok', [0]
        yield 'expanded-bound', 6, words([32]) + array(values), 'invalid', []
        yield 'fill', 7, words([32]) + array(values), 'ok', [2] * len(values)
    for index, data in ((0, b''), (1, words([32])), (1, words([MASK])),
                        (2, words([64, 0, 1])), (3, words([MASK, 0, 0])),
                        (4, words([64, 0, 2**32+1]))):
        yield 'malformed', index, data, 'revert', []


def scenario(_kind, caller, layout, *, initial_count=3, functions=None,
             fields=None, errors=None, **_):
    functions = functions or FUNCTIONS
    fields = fields or ('links', 'capacity', 'revision')
    slots = {f['label']: int(f['slot']) for f in layout['storage']}
    mapping = lambda key: int.from_bytes(keccak(bytes.fromhex(word(key)[2:] + word(slots[fields[0]])[2:])), 'big')
    # Explicitly arbitrary starting states: include malformed lists and dirty words.
    links = {1: (1 << 200) + 11, 11: 12, 12: 13, 13: 1, 0: 0}
    if errors == 'cycle':
        links[13] = 11
    elif errors == 'missing':
        links[13] = 0
    elif errors == 'empty':
        links[1] = 1
    current = {int(f['slot']): 0 for f in layout['storage']}
    current[slots[fields[1]]] = initial_count
    current[slots[fields[2]]] = 7
    current[9999] = 0xABCDE
    current.update({mapping(key): value for key, value in links.items()})
    initial = [(caller, word(slot), word(value)) for slot, value in sorted(current.items())]
    calls, expected = [], {}
    rows = list(cases()) if len(functions) > 1 else []
    status, values = enumeration(initial_count, links)
    rows.append(('enumerate', len(functions)-1, b'', status, values))
    for label, index, data, status, values in rows:
        signature = functions[index]
        ident = str(len(calls))
        calls.append({'id': ident, 'label': label, 'function': signature.split('(')[0],
            'args': [int.from_bytes(data[i:i+32], 'big') for i in range(0, len(data), 32)],
            'sender': SENDER, 'target': caller, 'value': '0x0',
            'data': '0x' + (keccak(text=signature)[:4] + data).hex(),
            'timestamp': 1000000100 + len(calls), 'blockNumber': 2 + len(calls)})
        logs = []
        if status == 'ok' and index == 3 and len(functions) > 1:
            current[slots[fields[2]]] += 1
            logs = [event(caller, 'Attempt(uint256)', ['uint256'], [int.from_bytes(data[32:64], 'big')])]
        output = encoded_array(values) if index in (0, 1, 3, 7) or index == len(functions)-1 else word(values[0]) if values else '0x'
        expected[ident] = {'status': status, 'data': output if status == 'ok' else '0x',
            'events': logs, 'storage': [[caller, word(slot), word(value)] for slot, value in sorted(current.items())]}
    return initial, calls, expected


def run(output, **kwargs):
    return campaign(output, kind='memory-arrays', fixture=FIXTURE, contract='LegacyMemoryArrays',
                    functions=FUNCTIONS, scenario_builder=scenario, **kwargs)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--context', type=int, default=0)
    parser.add_argument('--initial-count', type=int, default=3)
    parser.add_argument('--errors', choices=('cycle', 'missing', 'empty'))
    raise SystemExit(run(**vars(parser.parse_args())))
