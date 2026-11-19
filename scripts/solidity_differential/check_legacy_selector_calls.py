"""Compare selector CALL frames, source guards and rollback on the Istanbul EVM and in Denote."""
import argparse
import json
from pathlib import Path

from eth_abi import decode, encode
from eth_utils import keccak

from .anvil import Anvil
from .check_external_code_and_low_level_call import RESPONDER, SENDER, address
from .check_interface_word_static_call import roots
from .engine import ROOT, SOLC, HarnessError, command, solc_compile, source_compiler, write_json
from .stateful import validate_observation

FIXTURE = ROOT / 'Contracts/SolidityImportSmoke/LegacySelectorCall.sol'
MODEL = FIXTURE.with_name('LegacySelectorCallModel.lean')
PROFILE = {'optimizer': {'enabled': True, 'runs': 800}, 'evmVersion': 'istanbul',
           'metadata': {'bytecodeHash': 'none'}}
# Response word, child reverts, byte length. The last account has no code.
RESPONSES = [(0, False, 0), (1, False, 32), (0, False, 32), (0xab << 248, False, 1),
             (0xdeadbeef << 224, True, 4), (2, False, 96), (1, True, 96), None]


def compile_input(out, name, source, language, binary, fields):
    unit = name + ('.sol' if language == 'Solidity' else '.yul')
    request = {'language': language, 'sources': {unit: {'content': source}},
               'settings': {**PROFILE, 'outputSelection': {'*': {'*': fields}}}}
    products = solc_compile(request, ROOT, out / name, solc=binary)['contracts'][unit]
    if len(products) != 1:
        raise HarnessError(f'expected a single {name} contract')
    return next(iter(products.values()))['evm']


def word(n):
    return '0x' + n.to_bytes(32, 'big').hex()


def frames(accounts):
    caller = address(0)
    for i, (child, response) in enumerate(zip(accounts, RESPONSES, strict=True)):
        value, failed, size = response or (0, False, 0)
        # The responder stores its word at zero; memory at 0x40 holds its free pointer.
        returned = (value.to_bytes(32, 'big') + bytes(32) + (128).to_bytes(32, 'big'))[:size]
        for method in ['inspect', 'checked']:
            # Vary both arguments so a swapped, truncated or stale payload is observable.
            receiver, amount = accounts[(i + 1) % len(accounts)], (1 << 250) + i
            args = encode(['address', 'address', 'uint256'], [child, receiver, amount])
            signature = method + '(address,address,uint256)'
            data = keccak(text=signature)[:4] + args
            payload = keccak(text='record(address,uint256)')[:4] + encode(
                ['address', 'uint256'], [receiver, amount])
            slots = [(caller, word(0))] + [(child, word(n)) for n in range(9)]
            yield method, child, data, payload, failed, returned, slots


def evm(out, bytecode, runtime, accounts):
    caller = address(0)
    rows = []
    attempts = 0
    with Anvil(out, hardfork='istanbul') as node:
        tx = {'from': SENDER, 'gas': hex(8_000_000), 'gasPrice': hex(2_000_000_000)}
        deployed = node.transact({**tx, 'data': '0x' + bytecode})['receipt']
        if deployed['status'] != '0x1' or deployed['contractAddress'] != caller:
            raise HarnessError('caller deployment failed')
        for child, config in zip(accounts, RESPONSES, strict=True):
            if config is not None:
                node.rpc('anvil_setCode', child, runtime)
                for n, value in enumerate(config):
                    node.rpc('anvil_setStorageAt', child, word(n), word(value))
            elif node.rpc('eth_getCode', child, 'latest') != '0x':
                raise HarnessError('empty target unexpectedly has code')
        for i, (method, child, data, payload, failed, returned, slots) in enumerate(frames(accounts)):
            record = node.transact({**tx, 'to': caller, 'data': '0x' + data.hex()})
            children = record['call'].get('calls', [])
            if len(children) != 1:
                raise HarnessError(f'{i}: expected one child CALL')
            frame = children[0]
            if (frame['type'], frame['from'], frame['to'], int(frame['value'], 16), frame['input'],
                frame.get('output', '0x'), 'error' in frame) != (
                    'CALL', caller, child, 0, '0x' + payload.hex(), '0x' + returned.hex(), failed):
                raise HarnessError(f'{i}: child calldata, success or raw returndata differs')
            row = node.observe(record, str(i), slots)
            writes = int(not failed and child != accounts[-1])
            if method == 'inspect':
                if row['status'] != 'ok':
                    raise HarnessError(f'{i}: raw observation reverted')
                ok, size, *words = decode(['bool', 'uint256'] + ['bytes32'] * 3,
                                          bytes.fromhex(row['data'][2:]))
                if (ok, size, b''.join(words)[:size]) != (not failed, len(returned), returned):
                    raise HarnessError(f'{i}: raw tuple differs')
            else:
                short = 0 < len(returned) < 32
                accepted = not failed and (not returned or (not short and any(returned[:32])))
                reason = keccak(text='Error(string)')[:4] + encode(['string'], ['response rejected'])
                expected = ('ok', '0x') if accepted else (
                    'revert', '0x' if short and not failed else '0x' + reason.hex())
                if (row['status'], row['data']) != expected:
                    raise HarnessError(f'{i}: short-circuit or source revert differs')
                attempts += int(accepted)
                writes *= 1 + int(accepted)
            _, storage = validate_observation(row)
            if int(storage[(caller, word(0))], 16) != attempts or int(storage[(child, word(3))], 16) != writes:
                raise HarnessError(f'{i}: caller or child storage commit/rollback differs')
            rows.append(row)
    return rows


def observation(row):
    return row['id'], row['status'], row['data'], row['events'], validate_observation(row)


def campaign(out):
    out.mkdir(parents=True, exist_ok=False)
    command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
             'Compiler.SolidityImport.SequenceRunner', 'Compiler.SolidityImport.Differential',
             'Compiler.SolidityImport.CallResponderMocks', 'Compiler.Codegen',
             'Compiler.Yul.PrettyPrint', '--project-dir', ROOT], timeout=1800, log=out / 'build.log')
    _, legacy = source_compiler({'solc': '0.7.6+commit.7338295f'})
    unit = FIXTURE.name
    source = solc_compile({'language': 'Solidity', 'sources': {unit: {'content': FIXTURE.read_text()}},
        'settings': {**PROFILE, 'outputSelection': {'*': {FIXTURE.stem: [
            'evm.bytecode.object', 'evm.methodIdentifiers']}}}}, ROOT, out / 'original',
        solc=legacy)['contracts'][unit][FIXTURE.stem]['evm']
    responder = compile_input(out, 'Responder', (ROOT / RESPONDER).read_text(), 'Solidity', SOLC,
                              ['evm.deployedBytecode.object'])
    runtime = '0x' + responder['deployedBytecode']['object']
    accounts = [address(i + 1) for i in range(len(RESPONSES))]
    original = evm(out / 'original-node', source['bytecode']['object'], runtime, accounts)
    transactions = []
    for i, (method, _, data, _, _, _, slots) in enumerate(frames(accounts)):
        transactions.append({'id': str(i), 'function': method, 'sender': str(int(SENDER, 16)),
            'target': str(int(address(0), 16)), 'value': '0', 'selector': str(int.from_bytes(data[:4], 'big')),
            'args': [str(int.from_bytes(data[j:j+32], 'big')) for j in range(4, len(data), 32)],
            'blockNumber': str(i+2), 'timestamp': str(1000000000+i+2),
            'observe': [[str(int(a, 16)), str(int(slot, 16))] for a, slot in slots]})
    ids = [str(int(a, 16)) for a in accounts]
    write_json(out / 'input.json', {'account': str(int(address(0), 16)), 'storage': [],
        'transactions': transactions, 'accountCode': [[a, runtime] for a in ids[:-1]],
        'externalStorage': [[a, str(i), str(int(v))] for a, cfg in zip(ids, RESPONSES, strict=True)
                            if cfg is not None for i, v in enumerate(cfg)],
        'byteCallEnvironment': {'program': 'recording-call-responder-v1', 'gas': '1000000',
                                'accounts': ids[:-1], 'emptyAccounts': ids[-1:]}})
    selectors = [int(source['methodIdentifiers'][s], 16) for s in roots(MODEL.read_text())]
    paths = [json.dumps(str(out / name)) for name in ('model.yul', 'input.json', 'model.json')]
    driver = out / 'Replay.lean'
    driver.write_text(MODEL.read_text() +
        f'\n#eval SolidityImportSmoke.LegacySelectorCall.compileAndRun {selectors} ' + ' '.join(paths) + '\n')
    command(['turbo-lean', 'eval', driver, '--project-dir', ROOT, '--timeout-ms', '180000'],
            timeout=210, log=out / 'eval.log')
    generated = compile_input(out, 'Generated', (out / 'model.yul').read_text(), 'Yul', SOLC,
                              ['evm.bytecode.object'])
    compiled = evm(out / 'generated-node', generated['bytecode']['object'], runtime, accounts)
    model = json.loads((out / 'model.json').read_text())
    for a, b, c in zip(original, model, compiled, strict=True):
        if observation(a) != observation(b) or observation(b) != observation(c):
            raise HarnessError(f'{a["id"]}: original/model/generated observations differ')
    write_json(out / 'comparisons.json', {'original': original, 'model': model, 'generated': compiled})
    print('Selector calldata, raw result tuples, source guards and rollback agree.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    campaign(parser.parse_args().output.resolve())
