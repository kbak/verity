"""Source-only controls for loop development, not importer/correspondence evidence.

Expected walk results use a closed-form count; search records repeated states.
EVM resource exhaustion remains distinct from Solidity REVERT/INVALID and from
observer exhaustion. Small concrete cycle witnesses are not a general loop proof.
"""
import argparse
import hashlib
from pathlib import Path

from eth_abi import encode
from eth_utils import keccak

from .anvil import Anvil
from .engine import HarnessError, solc_compile, write_json

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyLoopControl.sol')
MASK = (1 << 256) - 1
GAS = 150000
WALK = 'walk(uint256,uint256,uint256,uint256,int24)'
SEARCH = 'search(uint256,uint256,uint256,uint256)'


def search_path(low, high, target, skip_mask):
    """Concrete unsigned source-state transitions, with a retained cycle witness."""
    seen, path = {}, []
    while (low, high) not in seen:
        if len(path) >= 128:
            raise HarnessError('search oracle limit reached; result is unknown')
        seen[low, high] = len(path)
        middle = ((low + high) & MASK) // 2
        path.append([low, high, middle])
        skipped = middle < 256 and (skip_mask >> middle) & 1
        if skipped:
            low = (middle + 1) & MASK
        elif middle == target:
            return {'value': middle, 'path': path}
        elif middle > target:
            high = (middle - 1) & MASK
        else:
            low = (middle + 1) & MASK
    return {'cycleStart': seen[low, high], 'repeated': [low, high], 'path': path}


def run(output, optimized=False):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = FIXTURE.read_text()
    (output / FIXTURE.name).write_text(source)
    compiled = solc_compile({'language': 'Solidity',
        'sources': {FIXTURE.name: {'content': source}}, 'settings': {
            'evmVersion': 'istanbul', 'optimizer': {'enabled': optimized, 'runs': 800},
            'metadata': {'bytecodeHash': 'none'},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}},
        output, output / 'solc', solc=Path.cwd() / '.lake/solidity-import/solc-0.7.6')
    contract = compiled['contracts'][FIXTURE.name]['LegacyLoopControl']
    rows, effects = [], 0
    with Anvil(output / 'node') as node:
        sender = node.rpc('eth_accounts')[0]
        deployment = node.transact({'from': sender, 'data': '0x' +
            contract['evm']['bytecode']['object'], 'gas': hex(1000000)})
        if deployment['receipt']['status'] != '0x1':
            raise HarnessError('loop fixture deployment failed')
        account = deployment['receipt']['contractAddress']

        def execute(signature, args):
            data = contract['evm']['methodIdentifiers'][signature]
            data += ''.join((n & MASK).to_bytes(32, 'big').hex() for n in args)
            record = node.transact({'from': sender, 'to': account,
                                    'data': '0x' + data, 'gas': hex(GAS)})
            call, receipt = record['call'], record['receipt']
            error = call.get('error')
            status = 'ok' if receipt['status'] == '0x1' else 'revert'
            if error and 'out of gas' in error.lower():
                if receipt['status'] != '0x0' or int(receipt['gasUsed'], 16) != GAS:
                    raise HarnessError('inconsistent resource-exhaustion trace')
                status = 'resource-exhausted'
            elif status == 'revert' and error != 'execution reverted':
                raise HarnessError(f'unexpected exceptional halt: {error}')
            elif status == 'ok' and error:
                raise HarnessError('successful receipt has a trace error')
            stored = int(node.rpc('eth_getStorageAt', account, '0x0', receipt['blockNumber']), 16)
            return {'status': status, 'data': call.get('output', '0x'), 'effects': stored}

        for args in [(0, 0, 0, 0, -2), (1, 0, 0, 0, -2), (5, 2, 4, 0, -2),
                     (3, 2, 2, 0, -2), (5, 2, 4, 5, -2), (5, 2, 4, 3, -2),
                     (5, 2, 4, 2, -2), (2, 0, 0, 0, 8388607),
                     (3, 0, 0, 0, -8388608)]:
            count, skip, stop, fail, delta = args
            last = stop if 1 <= stop <= count and stop != skip else count
            if 1 <= fail <= last:
                wanted = {'status': 'revert', 'data': '0x' +
                    (keccak(text='Error(string)')[:4] + encode(['string'], ['loop'])).hex(),
                    'effects': effects}
            else:
                terms = last - int(1 <= skip <= last)
                total = (terms * delta) % (1 << 24)
                if total >= (1 << 23):
                    total -= 1 << 24
                effects += last + 100
                wanted = {'status': 'ok', 'data': '0x' + encode(['int24'], [total]).hex(),
                          'effects': effects}
            actual = execute(WALK, args)
            rows.append({'function': 'walk', 'args': args, 'expected': wanted, 'actual': actual})
        for args in [(0, 7, 3, 0), (0, 7, 0, 0), (0, 7, 7, 0), (0, 7, 5, 1 << 3),
                     (0, 7, 7, MASK)]:
            oracle = search_path(*args)
            wanted = {'effects': effects, 'status': 'ok' if 'value' in oracle else 'resource-exhausted',
                      'data': '0x' + encode(['uint256'], [oracle['value']]).hex()
                              if 'value' in oracle else '0x'}
            actual = execute(SEARCH, args)
            rows.append({'function': 'search', 'args': args, 'oracle': oracle,
                         'expected': wanted, 'actual': actual})
    failures = [row for row in rows if row['actual'] != row['expected']]
    write_json(output / 'results.json', {'passed': not failures, 'rows': rows, 'failures': failures,
        'optimized': optimized, 'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
        'gasLimit': GAS, 'scope': 'source-only concrete controls; no importer or correspondence claim'})
    if failures:
        raise HarnessError('loop source controls differ from independent expectations')
    print('loop source controls passed')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    run(**vars(parser.parse_args()))
