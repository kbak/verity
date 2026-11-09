"""Legacy recovery and bytes4 validators: source EVM / Denote / compiled EVM.

The precompile oracle uses eth-keys' independent native Python secp256k1 backend,
not responses recorded from either EVM. Contract mocks hash the complete calldata.
Gas and cryptographic correctness proofs are outside this finite campaign.
"""
import argparse
import hashlib
from pathlib import Path
import random
import sys

from eth_abi import encode
from eth_keys import keys
from eth_keys.backends import NativeECCBackend
from eth_keys.constants import SECPK1_N
from eth_keys.exceptions import BadSignature
from eth_utils import keccak

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import SOLC, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes
from .check_interface_word_static_call import address, roots, SENDER, EMPTY

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacySignatureCalls.sol')
DRIVER = FIXTURE.with_name('LegacySignatureCallsModel.lean')
ORACLE = FIXTURE.with_name('SignatureCallOracle.sol')
ANCHOR = 'from "Contracts/SolidityImportSmoke" entry "LegacySignatureCalls.sol"'
MASK = (1 << 256) - 1
MAGIC = 0x1626BA7E << 224
RESPONSES = [(MAGIC, False, 32, 0), (MAGIC + 1, False, 32, 0),
             (MASK, False, 32, 0), (0, False, 32, MASK),
             (MAGIC, False, 0, 0), (MAGIC, False, 4, 0),
             (MAGIC, False, 31, 0), (MAGIC + 1, False, 65, 0),
             (0x1234, True, 0, 0), (0x1234, True, 4, 0),
             (MASK, True, 33, 0), (MASK, True, 100, 0)]
BACKEND = NativeECCBackend()


def recovery(h, v, r, s):
    """Ethereum's v=27/28 convention, including valid high-s signatures."""
    if v not in (27, 28) or not 0 < r < SECPK1_N or not 0 < s < SECPK1_N:
        return []
    try:
        signature = keys.Signature(vrs=(v - 27, r, s), backend=BACKEND)
        return [int.from_bytes(signature.recover_public_key_from_msg_hash(h).to_canonical_address(), 'big')]
    except BadSignature:
        return []


def validator_expectation(target, h, data, method, enabled, accounts):
    """Independent ABI and mock-memory expectations, including exact failures."""
    def result(status, payload):
        return status, '0x' + payload.hex()
    def words(*values):
        return result('ok', encode(['uint256'] * len(values), list(values)))
    if method == 'gated' and not enabled:
        return words(0)
    if target not in accounts:
        return result('revert', b'')
    value, failed, length, mask = RESPONSES[accounts.index(target)]
    selector = ('validate' if method in ('word', 'abstractWord', 'scratch') else
                'isValidSignature') + '(bytes32,bytes)'
    calldata = keccak(text=selector)[:4] + encode(['bytes32', 'bytes'], [h, data])
    raw = value ^ (int.from_bytes(keccak(calldata), 'big') & mask)
    memory = raw.to_bytes(32, 'big') + bytes(32) + (128).to_bytes(32, 'big') + bytes(32) + calldata
    response = memory.ljust(length, b'\0')[:length]
    if failed:
        return result('revert', response)
    if length < 32:
        return result('revert', b'')
    cleaned = raw & (((1 << 32) - 1) << 224)
    if method in ('word', 'abstractWord'):
        return words(cleaned)
    if method == 'scratch':
        return words(cleaned, raw)
    valid = cleaned == MAGIC
    if method == 'checked':
        return words(len(data)) if valid else result('revert',
            keccak(text='Error(string)')[:4] + encode(['string'], ['signature']))
    return words(int(valid))


def transactions(seed, caller, accounts, random_cases):
    rng = random.Random(seed)
    calls, oracle_rows, expectations = [], {}, {}

    def add(signature, values):
        types = signature[signature.index('(') + 1:-1].split(',')
        payload = encode(types, values)
        index = str(len(calls))
        calls.append({'id': index, 'function': signature.split('(')[0],
                      'args': [int.from_bytes(payload[i:i+32], 'big') for i in range(0, len(payload), 32)],
                      'sender': SENDER, 'target': caller, 'value': '0x0',
                      'data': '0x' + keccak(text=signature)[:4].hex() + payload.hex(),
                      'timestamp': 1000000100 + len(calls),
                      'blockNumber': len(accounts) + 2 + len(calls)})
        return index

    vectors = []
    for i in range(random_cases + 3):
        secret = rng.randrange(1, SECPK1_N)
        h = rng.getrandbits(256).to_bytes(32, 'big')
        key = keys.PrivateKey(secret.to_bytes(32, 'big'), backend=BACKEND)
        sig = key.sign_msg_hash(h)
        v, r, s = sig.v + 27, sig.r, sig.s
        vectors.extend([(h, v, r, s), (h, 55 - v, r, SECPK1_N - s),
                        (h, v + 256, r, s), (h, v, 0, s), (h, 0, r, s)])
        if i < 3:
            vectors.extend((h, bad, r, s) for bad in (1, 26, 29, 30, 31, 255, MASK))
            vectors.extend((h, v, bad, s) for bad in (SECPK1_N, MASK))
            vectors.extend((h, v, r, bad) for bad in (0, SECPK1_N, MASK))
    for h, v, r, s in vectors:
        for method in ('recover', 'twice', 'inspect'):
            ident = add(f'{method}(bytes32,uint256,bytes32,bytes32)',
                        [h, v, r.to_bytes(32, 'big'), s.to_bytes(32, 'big')])
            result = recovery(h, v % 256, r, s)
            args = (int.from_bytes(h, 'big'), v % 256, r, s)
            oracle_rows[args] = result
            value = result[0] if result else 0
            expected = [value] if method == 'recover' else [value, 0 if method == 'twice' else 160]
            expectations[ident] = ('ok', '0x' + encode(['uint256'] * len(expected), expected).hex())
            if method == 'twice':
                oracle_rows[(args[0], 0, r, s)] = []
    for h, v, r, s in vectors[:5]:
        for n in (0, 1, 3):
            ident = add('loop(bytes32,uint256,bytes32,bytes32,uint256)',
                        [h, v, r.to_bytes(32, 'big'), s.to_bytes(32, 'big'), n])
            value = (recovery(h, v % 256, r, s) or [0])[0] if n else 0
            expectations[ident] = ('ok', '0x' + encode(['uint256'], [value]).hex())
    targets = [*accounts, EMPTY, SENDER, *('0x' + '00' * 19 + v for v in ('01', '02'))]
    for target in targets:
        for length in (0, 1, 31, 32, 33, 65, 129):
            data = rng.randbytes(length)
            h = rng.randbytes(32)
            for method in ('word', 'abstractWord', 'scratch', 'check', 'checked'):
                ident = add(f'{method}(address,bytes32,bytes)', [target, h, data])
                expectations[ident] = validator_expectation(target, h, data, method, True, accounts)
            for enabled in (False, True):
                ident = add('gated(bool,address,bytes32,bytes)', [enabled, target, h, data])
                expectations[ident] = validator_expectation(target, h, data, 'gated', enabled, accounts)
    rows = [{'args': list(map(str, args)), 'output': list(map(str, result))}
            for args, result in sorted(oracle_rows.items())]
    return calls, rows, expectations


def campaign(directory, *, optimized=False, context=0, seed=2851, random_cases=4):
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=False)
    command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
             'Compiler.SolidityImport.Differential', 'Compiler.SolidityImport.SequenceRunner',
             'Compiler.SolidityImport.SignatureMocks', '--project-dir', '.'], timeout=1800,
            log=directory / 'build.log')
    source = FIXTURE.read_text()
    if context:
        source = source.replace('contract LegacySignatureCalls {',
            'contract LegacySignatureCalls {\n' + '\n'.join(f'uint256 private pad{i};' for i in range(context)))
    (directory / 'Sequence.sol').write_text(source)
    template = DRIVER.read_text()
    assert template.count(ANCHOR) == 1
    template = template.replace(ANCHOR, f'from "{directory}" entry "Sequence.sol"')
    if optimized:
        template = template.replace('optimizerRuns := none', 'optimizerRuns := some 200')
    driver = directory / 'Driver.lean'
    driver.write_text(template)
    settings = {'evmVersion': 'istanbul', 'optimizer': {'enabled': optimized, 'runs': 200},
                'metadata': {'bytecodeHash': 'none'}}
    source_contract = solc_compile({'language': 'Solidity',
        'sources': {'Sequence.sol': {'content': source}},
        'settings': {**settings, 'outputSelection': {'*': {'*': ['evm.bytecode.object',
            'evm.methodIdentifiers', 'storageLayout']}}}}, directory, directory / 'source-solc',
        solc=Path.cwd() / '.lake/solidity-import/solc-0.7.6')['contracts']['Sequence.sol']['LegacySignatureCalls']
    if len(source_contract['storageLayout']['storage']) != context:
        raise HarnessError('source state declaration count differs from requested context')
    identifiers = source_contract['evm']['methodIdentifiers']
    write_json(directory / 'selectors.json', [int(identifiers[s], 16) for s in roots(template)])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], timeout=900, log=directory / 'compile.log')
    model = solc_compile({'language': 'Yul',
        'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, directory,
        directory / 'model-solc', solc=SOLC)['contracts']['Model.yul']
    if len(model) != 1:
        raise HarnessError('expected one compiled model object')
    mock = solc_compile({'language': 'Solidity',
        'sources': {ORACLE.name: {'content': ORACLE.read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 466},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.deployedBytecode.object']}}}},
        directory, directory / 'oracle-solc', solc=SOLC)['contracts'][ORACLE.name]['SignatureCallOracle']['evm']
    caller = address(0)
    accounts = [address(i + 1) for i in range(len(RESPONSES))]
    deployments = ['0x' + mock['bytecode']['object'] +
                   encode(['uint256', 'bool', 'uint256', 'uint256'], list(p)).hex() for p in RESPONSES]
    initial = [(account, '0x' + slot.to_bytes(32, 'big').hex(),
                '0x' + int(value).to_bytes(32, 'big').hex())
               for account, parameters in zip(accounts, RESPONSES, strict=True)
               for slot, value in enumerate(parameters)]
    calls, recoveries, expectations = transactions(seed, caller, accounts, random_cases)
    write_json(directory / 'transactions.json', calls)
    environment = {'program': 'hash-static-oracle-v1', 'accounts': [str(int(a, 16)) for a in accounts],
                   'emptyAccounts': [str(int(EMPTY, 16)), str(int(SENDER, 16))],
                   'gas': '1000000', 'recoveries': recoveries}
    write_json(directory / 'environment.json', environment)
    adapters = {
        'source': EVM(directory / 'A', ['0x' + source_contract['evm']['bytecode']['object'], *deployments], initial),
        'model': Denote(directory / 'B', driver, caller, initial, byte_call_environment=environment,
            account_code=[(a, '0x' + mock['deployedBytecode']['object']) for a in accounts]),
        'compiled': EVM(directory / 'C', ['0x' + next(iter(model.values()))['evm']['bytecode']['object'], *deployments], initial)}
    result = replay_three_routes(calls, adapters)
    report = {**result, 'count': len(calls), 'optimized': optimized, 'context': context, 'seed': seed,
              'sourceSha256': hashlib.sha256(source.encode()).hexdigest()}
    write_json(directory / 'campaign.json', report)
    write_json(directory / 'results.json', {**report, 'cases': len(calls)})
    if result['divergences']:
        return 1
    for route, observations in result['observations'].items():
        for tx, observation in zip(calls, observations, strict=True):
            if tx['id'] in expectations:
                actual = observation['status'], observation['data']
                if actual != expectations[tx['id']]:
                    raise HarnessError(f'independent signature expectation differs: {route} {tx["id"]}')
    write_json(directory / 'summary.json', {'passed': True, 'count': len(calls),
        'optimized': optimized, 'context': context, 'seed': seed,
        'scope': 'finite byte-exact A/B/C observations; explicit external world; gas excluded'})
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--optimized', action='store_true')
    parser.add_argument('--context', type=int, choices=(0, 1, 2), default=0)
    parser.add_argument('--random-cases', type=int, default=4)
    parser.add_argument('--seed', type=int, default=2851)
    args = parser.parse_args()
    if args.random_cases < 0:
        parser.error('--random-cases must be nonnegative')
    return campaign(args.output, optimized=args.optimized, context=args.context,
                    seed=args.seed, random_cases=args.random_cases)


if __name__ == '__main__':
    sys.exit(main())
