"""Pinned, stateless hash execution adapters; no inferred expected results."""
import json
from pathlib import Path
import re
import shutil

from keccak256 import selector
from setup_solc_import import RELEASES, file_sha256, host_platform
from .anvil import Anvil
from .check_packed_memory_hash import SETTINGS, word
from .check_packed_memory_hash_import import classify, driver_text, evaluate
from .engine import HarnessError, ROOT, command, solc_compile, write_json

MARKER = 'HASH_EXECUTION_SNAPSHOT:'
YUL_SETTINGS = {'evmVersion': 'cancun', 'optimizer': SETTINGS['optimizer']}
TIMESTAMP = 1000000001


def checked_bytes(value):
    if not isinstance(value, str) or not re.fullmatch(r'0x(?:[0-9a-f]{2})*', value):
        raise HarnessError('missing or malformed byte observation')
    return bytes.fromhex(value[2:])


def pinned_compiler():
    path = ROOT / '.lake/solidity-import/solc-0.8.26'
    release = RELEASES['0.8.26']
    if not path.is_file() or file_sha256(path) != release['sha256'][host_platform()]:
        raise HarnessError('missing or changed pinned Solidity 0.8.26 compiler')
    banner = command([path, '--version']).strip()
    if f"Version: {release['long_version']}." not in banner:
        raise HarnessError('pinned compiler banner mismatch')
    return path, {'longVersion': release['long_version'], 'banner': banner,
                  'sha256': file_sha256(path)}


def validate_cases(signature, cases):
    if not cases or len({row['id'] for row in cases}) != len(cases):
        raise HarnessError('empty or duplicate case inventory')
    count = len(signature.split('(', 1)[1].removesuffix(')').split(','))
    for row in cases:
        args = row['args']
        if (len(args) != count or any(not isinstance(arg, str) or not arg.isdecimal()
                                     or not 0 <= int(arg) < 2**256 for arg in args)
                or row['timestamp'] != str(TIMESTAMP) or row['storage'] or row['observe']):
            raise HarnessError('invalid stateless hash input')
        data = selector(signature) + b''.join(word(int(arg)) for arg in args).hex()
        if checked_bytes(row['calldata']) != checked_bytes(data):
            raise HarnessError('selector/calldata differs from model argument words')
        if len(checked_bytes(row['expected'])) not in (32, 192):
            raise HarnessError('invalid independent hash expectation length')


def compile_source(directory, filename, contract, solc):
    source = (directory / filename).read_text()
    request = {'language': 'Solidity', 'sources': {filename: {'content': source}},
               'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
                   'abi', 'storageLayout', 'evm.methodIdentifiers',
                   'evm.bytecode.object', 'evm.deployedBytecode.object']}}}}
    result = solc_compile(request, directory, directory / 'source', solc=solc)
    built = result['contracts'][filename][contract]
    if built['storageLayout']['storage'] or any(
            item['type'] == 'constructor' for item in built['abi']):
        raise HarnessError('hash harness requires empty storage and no constructor')
    return built


def verify_abi(built, signature, cases):
    name, types = signature.split('(', 1)
    types = types[:-1].split(',')
    matches = [item for item in built['abi'] if item['type'] == 'function'
               and item['name'] == name and [p['type'] for p in item['inputs']] == types]
    if (len(matches) != 1 or matches[0]['stateMutability'] != 'pure'
            or any(p['type'] not in ('bytes32', 'uint256') for p in matches[0]['outputs'])
            or len(matches[0]['outputs']) * 32 != len(checked_bytes(cases[0]['expected']))
            or built['evm']['methodIdentifiers'].get(signature) != selector(signature)[2:]):
        raise HarnessError('source ABI/selector does not match the pinned hash experiment')


def code_bytes(built, key):
    code = checked_bytes('0x' + built['evm'][key]['object'])
    if not code:
        raise HarnessError('compiler returned empty bytecode')
    return code


def execute_evm(directory, built, cases, expected_context=None):
    """Deploy once on a fresh Cancun node; each eth_call starts from that same state."""
    directory.mkdir()
    creation, runtime = code_bytes(built, 'bytecode'), code_bytes(built, 'deployedBytecode')
    (directory / 'creation.bin').write_bytes(creation)
    (directory / 'runtime.bin').write_bytes(runtime)
    observations = []
    with Anvil(directory / 'node', hardfork='cancun') as node:
        sender = node.rpc('eth_accounts')[0]
        if node.rpc('eth_getTransactionCount', sender, 'latest') != '0x0':
            raise HarnessError('deployment account is not fresh')
        node.rpc('evm_setNextBlockTimestamp', TIMESTAMP)
        deployment = node.transact({'from': sender, 'data': '0x' + creation.hex(),
                                    'value': '0x0', 'gas': hex(10000000)})
        receipt = deployment['receipt']
        if receipt.get('status') != '0x1' or not receipt.get('contractAddress'):
            raise HarnessError('hash fixture deployment failed')
        target = receipt['contractAddress']
        block = node.rpc('eth_getBlockByHash', receipt['blockHash'], False)
        context = {'sender': int(sender, 16), 'txOrigin': int(sender, 16),
                   'thisAddress': int(target, 16), 'msgValue': 0,
                   'blockTimestamp': int(block['timestamp'], 16),
                   'blockNumber': int(block['number'], 16),
                   'chainId': int(node.rpc('eth_chainId'), 16)}
        if (context['blockTimestamp'] != TIMESTAMP or context['blockNumber'] != 1
                or context['chainId'] != 31337
                or (expected_context is not None and context != expected_context)
                or checked_bytes(node.rpc('eth_getCode', target, 'latest')) != runtime
                or int(node.rpc('eth_getBalance', target, 'latest'), 16) != 0):
            raise HarnessError('deployed runtime or initial call environment differs')
        for case in cases:
            actual = node.rpc('eth_call', {'from': sender, 'to': target,
                              'data': case['calldata'], 'value': '0x0',
                              'gas': hex(10000000)}, receipt['blockNumber'])
            checked_bytes(actual)
            observations.append({'id': case['id'], 'status': 'ok', 'data': actual})
        write_json(directory / 'environment.json', {
            'context': context, 'initialStorage': [], 'initialBalance': '0',
            'callMode': 'eth_call at the deployment block; no state is carried between calls',
            'node': node.provenance, 'anvilSha256': file_sha256(Path(shutil.which('anvil'))),
            'observations': 'pure static ABI returns; gas, balances and storage frames not compared'})
    write_json(directory / 'observations.json', observations)
    return observations, context


def import_root(directory, filename, contract, signature):
    driver = directory / 'admission.lean'
    driver.write_text(driver_text(directory.parent, filename, contract, signature))
    code, reply = evaluate(driver)
    observation = classify(code, reply, (directory.parent / filename).read_text(),
                           filename, contract, signature.split('(')[0])
    write_json(directory / 'admission.json', observation)
    return observation


def validate_snapshot(snapshot, signature, cases, compiler):
    for key in ('model', 'report', 'digest', 'yul', 'compilerProof', 'context'):
        if not isinstance(snapshot.get(key), str) or not snapshot[key]:
            raise HarnessError('missing model provenance or generated code')
    if (snapshot.get('function') != signature.split('(')[0]
            or snapshot.get('targetFork') != 'cancun'
            or snapshot.get('selector') != int(selector(signature), 16)
            or snapshot.get('denoteCovered') is not True
            or snapshot.get('solcLongVersion') != compiler['longVersion']
            or snapshot.get('solcSha256') != compiler['sha256']
            or not isinstance(snapshot.get('params'), list)
            or len(snapshot['params']) != len(cases[0]['args'])
            or not re.fullmatch(r'[0-9a-f]{64}', snapshot['digest'])):
        raise HarnessError('model compiler/profile/selector/provenance mismatch')
    settings = json.loads(snapshot['settings'])
    if (not isinstance(settings, dict)
            or any(settings.get(key) != value for key, value in SETTINGS.items())
            or set(settings) - set(SETTINGS) - {'outputSelection', 'remappings'}
            or settings.get('remappings', []) != []):
        raise HarnessError('imported source profile changed')
    rows = snapshot.get('results')
    validate_observations(rows, cases)
    for row in rows:
        values = row.get('words')
        if (not isinstance(values, list) or any(not isinstance(n, str) or not n.isdecimal()
                or not 0 <= int(n) < 2**256 for n in values)
                or b''.join(word(int(n)) for n in values) != checked_bytes(row['data'])
                or row.get('storage') != []):
            raise HarnessError('model words/bytes/state observations disagree')


def snapshot_root(directory, filename, contract, signature, cases, context, compiler):
    """Embed inputs in the eval driver: cached stdout is a complete immutable artifact."""
    driver = directory / 'snapshot.lean'
    frame = {**context, 'functionSelector': int(selector(signature), 16)}
    fields = ', '.join(f'{key} := {value}' for key, value in frame.items())
    # Inputs are JSON strings. Lean decodes this exact literal; no Python-built model is used.
    payload = json.dumps(cases, separators=(',', ':'))
    driver.write_text(
        'import Compiler.SolidityImport.Differential\n'
        + driver_text(directory.parent, filename, contract, signature)
        + '#eval do\n'
        + f'  let input ← IO.ofExcept (Lean.Json.parse {json.dumps(payload)})\n'
        + '  let result ← IO.ofExcept '
          '(Compiler.CompilationModel.SolidityImport.Differential.snapshotRoot\n'
        + f'    imported.model imported.report {json.dumps(signature.split("(")[0])} .cancun\n'
        + f'    {{ {fields}, args := [] }} input)\n'
        + f'  IO.println ({json.dumps(MARKER)} ++ result.compress)\n')
    code, reply = evaluate(driver)
    if (code != 0 or reply.get('ok') is not True or reply.get('import_ok') is not True
            or reply.get('crashed') is not False or reply.get('timed_out') is not False
            or reply.get('errors') != []):
        raise HarnessError('admitted root failed actual model execution/code generation')
    lines = (reply.get('stdout', '') + '\n' + '\n'.join(reply.get('messages', []))).splitlines()
    artifacts = [line[len(MARKER):] for line in lines if line.startswith(MARKER)]
    if len(artifacts) != 1:
        raise HarnessError('missing or duplicate model execution snapshot')
    snapshot = json.loads(artifacts[0])
    write_json(directory / 'snapshot.json', snapshot)
    validate_snapshot(snapshot, signature, cases, compiler)
    (directory / 'model.yul').write_text(snapshot['yul'])
    write_json(directory / 'denote-observations.json', snapshot['results'])
    return snapshot


def compile_generated(directory, snapshot, solc):
    request = {'language': 'Yul', 'sources': {'Model.yul': {'content': snapshot['yul']}},
               'settings': {**YUL_SETTINGS, 'outputSelection': {'*': {'*': [
                   'evm.bytecode.object', 'evm.deployedBytecode.object']}}}}
    result = solc_compile(request, directory, directory / 'compiled', solc=solc)
    contracts = list(result['contracts']['Model.yul'].values())
    if len(contracts) != 1:
        raise HarnessError('expected exactly one generated Yul object')
    return contracts[0]


def validate_observations(rows, cases):
    if (not isinstance(rows, list) or len(rows) != len(cases)
            or any(not isinstance(row, dict) for row in rows)
            or [row.get('id') for row in rows] != [case['id'] for case in cases]):
        raise HarnessError('missing, duplicate, reordered or extra execution observations')
    for row, case in zip(rows, cases):
        if row.get('status') != 'ok':
            raise HarnessError('unexpected execution failure in a successful hash case')
        if len(checked_bytes(row.get('data'))) != len(checked_bytes(case['expected'])):
            raise HarnessError('unexpected ABI return size')


def compare_expectations(rows, cases, mutant=False):
    validate_observations(rows, cases)
    mismatches = [row['id'] for row, case in zip(rows, cases) if row['data'] != case['expected']]
    hashes = [row['id'] for row, case in zip(rows, cases)
              if row['data'][:66] != case['expected'][:66]]
    if (not mutant and mismatches) or (mutant and len(hashes) != len(cases)):
        raise HarnessError('independent expectation or mandatory mutation detection failed')
    return {'calls': len(rows), 'mismatches': mismatches, 'hashMismatches': hashes}


def compare_routes(routes, cases):
    if set(routes) != {'source', 'denote', 'compiled'}:
        raise HarnessError('all three real execution routes are required')
    for rows in routes.values():
        validate_observations(rows, cases)
    source = [row['data'] for row in routes['source']]
    if any([row['data'] for row in rows] != source for rows in routes.values()):
        raise HarnessError('source, actual Denote and generated EVM disagree')
