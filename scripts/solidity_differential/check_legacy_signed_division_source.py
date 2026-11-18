"""Original-bytecode controls for Solidity 0.7.6 signed division and remainder."""
import argparse
from pathlib import Path

from eth_abi import encode

from .anvil import Anvil
from .engine import HarnessError, solc_compile, source_compiler, write_json


FIXTURE = Path('Contracts/SolidityImportSmoke/LegacySignedDivision.sol')


def cases():
    # Explicit integer expectations distinguish truncation toward zero from floor
    # division and give the remainder the sign of the dividend.
    for x, y, quotient, remainder in [
        (-7, 3, -2, -1), (7, -3, -2, 1), (-7, -3, 2, -1), (7, 3, 2, 1),
        (-6, 3, -2, 0), (-1, 3, 0, -1), (0, -3, 0, 0),
    ]:
        yield 'guarded(int24,int24)', [x, y], 'ok', [quotient, remainder]
        yield 'choose(bool,int256,int256)', [True, x, y], 'ok', [quotient]
        yield 'choose(bool,int256,int256)', [False, x, y], 'ok', [remainder]
        yield 'guardedChoice(bool,int256,int256)', [True, x, y], 'ok', [quotient]
        yield 'guardedChoice(bool,int256,int256)', [False, x, y], 'ok', [remainder]
        yield 'fallbackOnZero(int24,int24)', [x, y], 'ok', [quotient]

    narrow_min = -(1 << 23)
    wide_min = -(1 << 255)
    yield 'guarded(int24,int24)', [narrow_min, -1], 'ok', [narrow_min, 0]
    yield 'choose(bool,int256,int256)', [True, wide_min, -1], 'ok', [wide_min]
    yield 'choose(bool,int256,int256)', [False, wide_min, -1], 'ok', [0]
    yield 'guarded(int24,int24)', [-7, 0], 'revert', []
    yield 'choose(bool,int256,int256)', [True, -7, 0], 'invalid', []
    yield 'choose(bool,int256,int256)', [False, -7, 0], 'invalid', []
    yield 'fallbackOnZero(int24,int24)', [-7, 0], 'ok', [-7]
    yield 'guardedChoice(bool,int256,int256)', [True, wide_min, -1], 'ok', [wide_min]
    yield 'guardedChoice(bool,int256,int256)', [False, wide_min, -1], 'ok', [0]
    yield 'guardedChoice(bool,int256,int256)', [False, wide_min, 0], 'revert', []
    for x, step, aligned in [(-17, 4, -16), (-16, 4, -16), (-1, 4, 0), (17, 4, 16)]:
        yield 'alignTowardZero(int24,int24)', [x, step], 'ok', [aligned]
    for step in (0, -4):
        yield 'alignTowardZero(int24,int24)', [17, step], 'revert', []
    yield 'byNegativeLiteral(int24)', [narrow_min], 'ok', [narrow_min, -2]
    yield 'byNegativeLiteral(int24)', [-7], 'ok', [7, -1]
    yield 'byNegativeLiteral(int24)', [7], 'ok', [-7, 1]
    yield 'selectAssignment(bool,int24,int24)', [True, -7, -5], 'ok', [7, 7]
    yield 'selectAssignment(bool,int24,int24)', [False, -7, -5], 'ok', [-5, -7]


def run(output, optimized):
    output.mkdir(parents=True, exist_ok=False)
    version, solc = source_compiler({'solc': '0.7.6+commit.7338295f'})
    request = {
        'language': 'Solidity',
        'sources': {FIXTURE.name: {'content': FIXTURE.read_text()}},
        'settings': {
            'evmVersion': 'istanbul', 'optimizer': {'enabled': optimized, 'runs': 800},
            'metadata': {'bytecodeHash': 'none'},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}},
        },
    }
    compiled = solc_compile(request, output, output / 'solc', solc=solc)
    evm = compiled['contracts'][FIXTURE.name][FIXTURE.stem]['evm']
    rows = []
    with Anvil(output / 'node', hardfork='istanbul') as node:
        sender = node.rpc('eth_accounts')[0]
        tx = {'from': sender, 'gas': hex(1_000_000), 'gasPrice': hex(2_000_000_000)}
        deployment = node.transact({**tx, 'data': '0x' + evm['bytecode']['object']})
        if deployment['receipt']['status'] != '0x1':
            raise HarnessError('signed division fixture deployment failed')
        account = deployment['receipt']['contractAddress']
        for signature, args, status, values in cases():
            types = signature.split('(')[1][:-1].split(',')
            data = evm['methodIdentifiers'][signature] + encode(types, args).hex()
            case = f'{signature} {args}'
            record = node.transact({**tx, 'to': account, 'data': '0x' + data})
            actual = node.observe(record, case)
            # The ABI sign-extends both narrow and full-width signed results to a word.
            expected = '0x' + encode(['int256'] * len(values), values).hex()
            rows.append({'case': case, 'expectedStatus': status, 'expectedData': expected,
                         'observation': actual})
            if (actual['status'], actual['data']) != (status, expected):
                raise HarnessError(f'{case}: expected {status} {expected}, got {actual}')
    write_json(output / 'results.json', {'compiler': version, 'settings': request['settings'],
                                         'route': 'source', 'cases': rows})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    run(**vars(parser.parse_args()))
