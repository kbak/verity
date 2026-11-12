"""Three-route native value calls, including discarded-return memory allocation."""
import argparse
import json
from pathlib import Path
from eth_abi import encode
from .anvil import Anvil
from .engine import SOLC, HarnessError, command, solc_compile, source_compiler, write_json
from .check_legacy_value_payments import FIXTURE, CHILDREN, EMPTY, child_code, address

MODEL = "Contracts.SolidityImportSmoke.LegacyNativeValueModel"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    _, solc = source_compiler({'solc': '0.7.6+commit.7338295f'})
    request = {'language': 'Solidity', 'sources': {FIXTURE.name: {'content': FIXTURE.read_text()}},
        'settings': {'evmVersion': 'istanbul', 'metadata': {'bytecodeHash': 'none'},
            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}}
    source = solc_compile(request, FIXTURE.parent, out / 'source', solc=solc)
    evm = source['contracts'][FIXTURE.name]['LegacyValuePayments']['evm']
    selector = evm['methodIdentifiers']['cursor(address)']
    # This gas-free model can be compiled; sourceGas=true models cannot.
    driver = out / 'Compile.lean'
    driver.write_text(f'import {MODEL}\nimport Compiler.CompilationModel\n'
        'import Compiler.Codegen\nimport Compiler.Yul.PrettyPrint\n'
        '#eval do\n  let result ← IO.ofExcept (Compiler.CompilationModel.compile '
        f'SolidityImportSmoke.LegacyNativeValueModel.model [{int(selector, 16)}] .osaka)\n'
        f'  IO.FS.writeFile {json.dumps(str(out / "model.yul"))} '
        '(Compiler.Yul.render (Compiler.emitYul result))\n')
    command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
            log=out / 'compile.log', timeout=210)
    generated = solc_compile({'language': 'Yul', 'sources': {'M.yul': {'content': (out / 'model.yul').read_text()}},
        'settings': {'evmVersion': 'osaka', 'optimizer': {'enabled': True, 'runs': 200},
            'outputSelection': {'*': {'*': ['evm.bytecode.object']}}}}, out, out / 'generated', solc=SOLC)
    compiled = next(iter(generated['contracts']['M.yul'].values()))['evm']['bytecode']['object']
    results = {}
    for route, bytecode in [('source', evm['bytecode']['object']), ('generated', compiled)]:
        rows, txs = [], []
        with Anvil(out / route / 'node') as node:
            sender = node.rpc('eth_accounts')[0]
            deployment = node.transact({'from': sender, 'data': '0x' + bytecode, 'gas': hex(10000000)})
            caller = deployment['receipt']['contractAddress']
            node.rpc('anvil_setBalance', caller, '0x64')
            for i, child in enumerate(CHILDREN):
                node.rpc('anvil_setCode', address(child), '0x' + child_code(i))
            for i, child in enumerate(CHILDREN + [EMPTY]):
                payload = encode(['address'], [address(child)])
                record = node.transact({'from': sender, 'to': caller,
                    'data': '0x' + selector + payload.hex(), 'gas': hex(300000)})
                block = node.rpc('eth_getBlockByHash', record['receipt']['blockHash'], False)
                rows.append({'id': str(i), 'status': 'ok' if record['receipt']['status'] == '0x1' else 'revert',
                    'data': record['call'].get('output', '0x'),
                    'balances': [int(node.rpc('eth_getBalance', a, 'latest'), 16)
                                 for a in [caller] + [address(a) for a in CHILDREN + [EMPTY]]]})
                txs.append({'id': str(i), 'function': 'cursor', 'args': [str(child)],
                    'selector': str(int(selector, 16)), 'sender': str(int(sender, 16)),
                    'target': str(int(caller, 16)), 'value': '0',
                    'timestamp': str(int(block['timestamp'], 16)),
                    'blockNumber': str(int(record['receipt']['blockNumber'], 16)), 'observe': [],
                    'observeAccounts': [str(a) for a in CHILDREN + [EMPTY]]})
        results[route] = rows
    if results['source'] != results['generated']:
        raise HarnessError('original/generated native call memory, result or balance differs')
    initial = {'account': str(int(caller, 16)), 'storage': [], 'accountNonce': '1',
        'initialBalances': [[str(int(caller, 16)), '100']],
        'accountCode': [[str(child), '0x' + child_code(i)] for i, child in enumerate(CHILDREN)],
        'paymentChildren': CHILDREN, 'emptyChildren': [EMPTY], 'transactions': txs}
    write_json(out / 'input.json', initial)
    driver = out / 'Replay.lean'
    driver.write_text(f'import {MODEL}\n#eval main ' + json.dumps(
        [str(out / 'input.json'), str(out / 'output.json')]) + '\n')
    command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
            log=out / 'model.log', timeout=210)
    rows = json.loads((out / 'output.json').read_text())
    if len(rows) != len(results['source']):
        raise HarnessError('model omitted native calls')
    for actual, want in zip(rows, results['source']):
        for key in ['id', 'status', 'data']:
            if actual[key] != want[key]:
                raise HarnessError('native model observation differs: ' + key)
        balances = [actual['deployment']['creator']['balance']] + [a['balance'] for a in actual['deployment']['accounts']]
        if balances != want['balances']:
            raise HarnessError('native model balances/rollback differ')
    write_json(out / 'complete.json', {'cases': len(rows), 'routes': ['original', 'Denote', 'generated']})
    print(f'{len(rows)} native call A/B/C cases passed')


if __name__ == '__main__':
    main()
