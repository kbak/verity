"""Legacy bool queries and fixed-slot installation: independent state/ABI expectations."""
import argparse
import random
from pathlib import Path
from eth_abi import encode
from eth_utils import keccak
from .check_legacy_raw_calls import campaign, FUNDS, MASK, SENDER, EMPTY
from .check_legacy_post_call_events import event

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyStaticInstallation.sol')
DRIVER = FIXTURE.with_name('LegacyStaticInstallationModel.lean')
ORACLE = FIXTURE.with_name('StaticBoolOracle.sol')
QUERY = 'acceptsTag(bytes4)'
MANY = 'assess(uint256,bytes32,address,bool,bytes4)'
READY = 'ready()'


def interface_id(signatures):
    value = 0
    for signature in signatures:
        value ^= int.from_bytes(keccak(text=signature)[:4], 'big')
    return value.to_bytes(4, 'big')


CAPABILITY = interface_id(('beforeAction(uint256)', 'afterAction(bytes32,bool)'))
PARENT = interface_id((QUERY, MANY, READY))


def encoded(signature, values):
    types = signature[signature.index('(')+1:-1].split(',') if values else []
    return keccak(text=signature)[:4] + encode(types, values)


def error(message):
    return encoded('Error(string)', [message])


def transactions(seed, caller, accounts, random_cases, *, slot=7, query=QUERY,
                 capability=CAPABILITY, install='install', read='readCandidate',
                 changed='Changed(address)', self_error='self', unsupported='unsupported',
                 extended=True, indexed_event=False):
    rng = random.Random(seed)
    balances = {caller: FUNDS, accounts[0]: 5, accounts[1]: 17, EMPTY: 0, SENDER: 1 << 200}
    nonces = {caller: 1, accounts[0]: 1, accounts[1]: 1, EMPTY: 0, SENDER: 3}
    storage, calls, expected = {}, [], {}
    changed_topic = int.from_bytes(keccak(text=changed), 'big')

    def response(target, data):
        if target not in accounts:
            return False, b'', 0
        word, length, mode, wanted = (storage.get((target, i), 0) for i in range(4))
        if wanted and wanted != int.from_bytes(keccak(data), 'big'):
            return False, bytes.fromhex('bad0ca11'), 0
        raw = (word.to_bytes(32, 'big') + bytes(32) + (128).to_bytes(32, 'big') + bytes(32))[:length]
        if mode >= 2:
            return False, b'', 0
        if mode == 1:
            return False, raw, 0
        if length < 32:
            return False, b'', 0
        return True, b'', word

    def add(signature, values, sender=SENDER, incoming=0, dirty=None, truncated=False):
        nonlocal storage
        data = encoded(signature, values)
        if dirty:
            offset, word = dirty
            data = data[:4+32*offset] + word.to_bytes(32, 'big') + data[36+32*offset:]
        if truncated:
            data = data[:20]
        payload = data[4:]
        payload += bytes((-len(payload)) % 32)
        ident = str(len(calls))
        method = signature.split('(')[0]
        calls.append({'id': ident, 'function': method,
            'args': [int.from_bytes(payload[i:i+32], 'big') for i in range(0, len(payload), 32)],
            'sender': sender, 'target': caller, 'value': hex(incoming), 'data': '0x' + data.hex(),
            'timestamp': 1000000400+len(calls), 'blockNumber': 4+len(calls)})
        saved = dict(storage)
        nonces[sender] += 1
        status, returned, logs = 'ok', b'', []
        if truncated or incoming:
            status = 'revert'
        elif method == 'seedResponse':
            target, word, length, mode, wanted = values
            if target not in accounts or length > 128 or mode > 3:
                status = 'revert'
            else:
                storage.update({(target, i): v for i, v in enumerate(
                    (word, length, mode, int.from_bytes(wanted, 'big')))})
        elif method in (install, 'installAndFail'):
            candidate = values[0]
            if method == 'installAndFail':
                storage[(caller, 0)] = 99
            if sender != caller:
                status, returned = 'revert', error(self_error)
            else:
                ok, failure, word = (True, b'', 1) if int(candidate, 16) == 0 else response(
                    candidate, encoded(query, [capability]))
                if not ok:
                    status, returned = 'revert', failure
                elif not word:
                    status, returned = 'revert', error(unsupported)
                else:
                    storage[(caller, slot)] = int(candidate, 16)
                    logs.append(event(caller, [changed_topic, int(candidate, 16)] if indexed_event else [changed_topic],
                                      b'' if indexed_event else encode(['address'], [candidate])))
                    if method == 'installAndFail':
                        status, returned = 'revert', error('late')
        elif method == read:
            returned = encode(['uint256'], [storage.get((caller, slot), 0) % (1 << 160)])
        elif method == 'readWord':
            returned = encode(['uint256'], [storage.get((caller, slot), 0)])
        elif method == 'storeWord':
            storage[(caller, slot)] = values[0]
        elif method == 'probePair':
            ok, failure, first = response(values[0], encoded(READY, []))
            if ok:
                ok, failure, second = response(values[1], encoded(READY, []))
            if not ok:
                status, returned = 'revert', failure
            else:
                returned = encode(['bool', 'bool'], [first != 0, second != 0])
        elif method == 'advertises':
            returned = encode(['bool'], [values[0][:4] in (CAPABILITY, PARENT)])
        else:
            target = values[0]
            request = encoded(query, values[1:]) if method == 'probe' else encoded(
                MANY if method == 'probeMany' else READY, values[1:])
            ok, failure, word = response(target, request)
            if not ok:
                status, returned = 'revert', failure
            elif method == 'probe':
                returned = encode(['uint256'] * 4, [int(word != 0), 128, 128, word])
            else:
                returned = encode(['bool'], [word != 0])
        if status != 'ok':
            storage, logs = saved, []
        expected[ident] = {'status': status, 'data': '0x'+returned.hex(), 'events': logs,
            'balances': dict(balances), 'nonces': dict(nonces),
            'storage': [[owner, key, value] for (owner, key), value in storage.items()]}

    def seed_response(target, word, length, mode, data=b''):
        wanted = keccak(data) if data else bytes(32)
        add('seedResponse(address,uint256,uint256,uint256,bytes32)',
            [target, word, length, mode, wanted])

    install_sig = install+'(address)'
    zero = '0x'+'00'*20
    query_data = encoded(query, [capability])
    add(install_sig, [accounts[0]])
    add(install_sig, [zero])
    add(install_sig, [zero], caller)
    add(read+'()', [])
    for target in accounts:
        for word in (0, 1, 2, 255, 1 << 255, MASK):
            for length in (0, 1, 4, 31, 32, 33, 65, 96):
                seed_response(target, word, length, 0, query_data)
                if extended:
                    add('probe(address,bytes32)', [target, capability])
                add(install_sig, [target], caller)
                add(read+'()', [])
        for mode in (1, 2, 3):
            for length in (0, 4, 31, 32, 33, 65, 96):
                seed_response(target, MASK, length, mode, query_data)
                add(install_sig, [target], caller)
                add(read+'()', [])
        seed_response(target, 1, 32, 0, b'wrong request')
        add(install_sig, [target], caller)
        seed_response(target, 1, 32, 0, query_data)
        add(install_sig, [target])
        add(install_sig, [target], caller, dirty=(0, int(target, 16)+(1 << 200)))
        if extended:
            add('installAndFail(address)', [target], caller)
            add(read+'()', [])
            add('readWord()', [])
    for target in (EMPTY, '0x'+'00'*19+'02', '0x'+'00'*19+'04'):
        add(install_sig, [target], caller)
        if extended:
            add('probe(address,bytes32)', [target, capability])
    add(install_sig, [zero], caller)
    add(read+'()', [])
    add(install_sig, [accounts[0]], SENDER, incoming=1)
    add(install_sig, [accounts[0]], caller, truncated=True)
    if extended:
        for word in (0, MASK, (1 << 200)+17):
            add('storeWord(uint256)', [word])
            add('readWord()', [])
            add(read+'()', [])
        for tag in (CAPABILITY, PARENT, bytes(4), b'\xff'*4,
                    bytes(a ^ b for a, b in zip(CAPABILITY, PARENT))):
            add('advertises(bytes32)', [tag])
        for i in range(random_cases):
            target = rng.choice(accounts)
            args = [rng.getrandbits(256), rng.randbytes(32), rng.choice(accounts), bool(i % 2), rng.randbytes(4)]
            seed_response(target, rng.choice([0, 1, 2, MASK]), 32, 0, encoded(MANY, args))
            add('probeMany(address,uint256,bytes32,address,bool,bytes32)', [target, *args])
        for word in (0, 2):
            seed_response(accounts[0], word, 65, 0, encoded(READY, []))
            add('probeEmpty(address)', [accounts[0]])
        for first, second in ((0, MASK), (2, 0), (2, MASK)):
            seed_response(accounts[0], first, 32, 0, encoded(READY, []))
            seed_response(accounts[1], second, 32, 0, encoded(READY, []))
            add('probePair(address,address)', accounts)
        seed_response(accounts[0], 1, 32, 0, encoded(READY, []))
        seed_response(accounts[1], 1, 31, 0, encoded(READY, []))
        add('probePair(address,address)', accounts)
        args = [19, bytes(32), accounts[1], True, CAPABILITY]
        seed_response(accounts[0], 1, 32, 0, encoded(MANY, args))
        add('probeMany(address,uint256,bytes32,address,bool,bytes32)', [accounts[0], *args],
            dirty=(4, MASK))
        seed_response(accounts[0], MASK, 65, 0, query_data)
        add('probe(address,bytes32)', [accounts[0], capability],
            dirty=(1, (int.from_bytes(capability, 'big') << 224) + 31))
    return calls, expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--seed', type=int, default=7601)
    parser.add_argument('--random-cases', type=int, default=12)
    args = parser.parse_args()
    return campaign(args.output, optimized=args.optimized, seed=args.seed,
        random_cases=args.random_cases, fixture=FIXTURE, driver_template=DRIVER,
        make_transactions=transactions, value_transactions=True, oracle_fixture=ORACLE,
        mock_module='StaticBoolMocks', mock_program='static-bool-oracle-v1', self_sender=True)


if __name__ == '__main__':
    raise SystemExit(main())
