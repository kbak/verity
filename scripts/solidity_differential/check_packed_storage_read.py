"""Prepare full-cleanup packed-hash/storage-read composition without changing admission."""
import argparse
import copy
import json
from pathlib import Path

from keccak256 import selector
from setup_solc_import import file_sha256
from .check_packed_memory_hash import SETTINGS, word
from .check_packed_memory_hash_import import observe
from .check_packed_memory_hash_routes import packed_cases, run_root
from .check_storage_reference import source_adapter
from .check_storage_reference_routes import STATE_ARCHIVES, control_inputs, require_outcome, run_routes
from .engine import HarnessError, ROOT, command, solc_compile, write_json
from .hash_execution import compile_generated, pinned_compiler
from .identity import ImplementationIdentity
from .pinned_sequence import SENDERS, create_address
from .storage_reference_oracle import PACKED_ARCHIVE_SHA256, SIGNATURES, replay_expected, specification
from .storage_sequence_execution import prepare_model

FIXTURE = ROOT / 'Contracts/SolidityImportSmoke/PackedStorageRead.sol'
CONTRACT = 'PackedStorageRead'
READ = SIGNATURES['read']
DIGEST = READ.replace('read(', 'digest(', 1)
KEY_READ = 'readKey(bytes32)'
COMPOSITION_REJECTION = 'bounded memory cannot observe synthetic allocation memory writes'


def read_prefix(spec):
    """Use only the six initial reads, without rewriting their independent expected observations."""
    result = copy.deepcopy(spec)
    result['transactions'] = result['transactions'][:6]
    result['expected'] = result['expected'][:6]
    if (len(result['transactions']) != 6 or len(result['expected']) != 6
            or any(tx['function'] != 'read' or tx['id'] != want['id']
                   or want['status'] != 'ok' or want['events']
                   or want['storage'] != spec['initialStorage']
                   for tx, want in zip(result['transactions'], result['expected']))):
        raise HarnessError('independent initial-read prefix changed')
    return result


def key_read_inputs(spec):
    """The separate supported control changes only selector/function/argument inputs."""
    result = control_inputs(spec)
    for tx in result['transactions']:
        tx['function'] = 'readKey'
        tx['data'] = selector(KEY_READ) + b''.join(word(n) for n in tx['args']).hex()
    return result


def source_variants(source):
    return {
        'original': source,
        'renamed': source.replace('packedKey', 'deriveKey').replace('locate', 'findRecord'),
        'shifted-layout': source.replace('uint256 private outerBefore;',
                                       'uint256 private extra; uint256 private outerBefore;'),
        'wrong-mapping-base': source.replace('uint256 private outerBefore;',
                                            'uint256[2] private outerBefore;'),
        'short-hash': source.replace('keccak256(add(base, 12), 58)',
                                    'keccak256(add(base, 12), 57)'),
    }


def rejected_sources(source):
    for name, before, after, reason in (
        ('partial-cleanup', '            mstore(base, 0)\n            mstore(add(base, 32), 0)\n',
         '', 'bounded memory leaves dirty scalar bytes visible after assembly'),
        ('dirty-hash', 'keccak256(add(base, 12), 58)', 'keccak256(base, 58)',
         'bounded memory hash observes dirty scalar bytes'),
        ('dirty-read', 'keccak256(add(base, 12), 58)', 'mload(base)',
         'bounded memory observes dirty scalar bits'),
        ('unknown-cleanup-alias', 'mstore(base, 0)', 'mstore(128, 0)',
         'bounded memory cannot establish disjointness from dirty bytes'),
    ):
        if source.count(before) != 1:
            raise HarnessError('rejection source anchor changed')
        yield name, source.replace(before, after), DIGEST, reason
    # This allocation has observable effects on the free pointer and synthetic memory layout.
    allocated = source.replace('        assembly ("memory-safe") {',
        '        bytes32 encoded = keccak256(abi.encode(salt));\n'
        '        assembly ("memory-safe") {', 1)
    allocated = allocated.replace('digest := keccak256(add(base, 12), 58)',
        'digest := xor(encoded, keccak256(add(base, 12), 58))', 1)
    yield 'abi-allocation', allocated, DIGEST, COMPOSITION_REJECTION
    observed = source.replace('Record storage row = locate(account, left, right, salt);',
        'Record storage row = locate(account, left, right, salt);\n'
        '        uint256 scratch;\n        assembly { scratch := mload(0) }')
    observed = observed.replace('return (row.count, row.accumulator, row.checkpoint);\n    }\n}',
        'return (row.count, row.accumulator, scratch);\n    }\n}')
    yield 'scratch-after-read', observed, READ, 'unsupported Yul builtin mload'


def compile_variant(directory, source, solc):
    directory.mkdir(parents=True, exist_ok=False)
    path = directory / FIXTURE.name
    path.write_text(source)
    result = solc_compile({'language': 'Solidity', 'sources': {path.name: {'content': source}},
        'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
            'abi', 'storageLayout', 'evm.methodIdentifiers',
            'evm.bytecode.object', 'evm.deployedBytecode.object']}}}},
        directory, directory / 'source', solc=solc)
    built = result['contracts'][path.name][CONTRACT]
    if (built['evm']['methodIdentifiers'] != {s: selector(s)[2:] for s in (READ, DIGEST, KEY_READ)}
            or any(item['type'] == 'constructor' for item in built['abi'])):
        raise HarnessError('read-only fixture ABI or constructor changed')
    return path, built


def require_rejection(observation, reason):
    if observation.get('status') != 'rejected' or observation.get('reason') != reason:
        raise HarnessError(f'expected located rejection {reason!r}, observed {observation}')


def require_source(result, mutant=False):
    if result.get('routes') != ['source'] or set(result.get('mismatches', {})) != {'source'}:
        raise HarnessError('missing actual source execution')
    rows = result['mismatches']['source']
    if (bool(rows) != mutant or any(row['fields'] != ['data'] for row in rows)):
        raise HarnessError('source read or mandatory return-data mutation evidence failed')


def run(output, *, prepared=False, require_composition=False):
    output = output.resolve()
    if not output.is_relative_to(ROOT):
        raise HarnessError('output must be inside the checkout')
    output.mkdir(parents=True, exist_ok=False)
    solc, compiler = pinned_compiler()
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.Differential', 'Compiler.SolidityImport.SequenceRunner',
                 '--project-dir', ROOT], cwd=ROOT, timeout=1800, log=output / 'build.log')
    identity = ImplementationIdentity(FIXTURE)
    specs = {shift: specification(create_address(SENDERS[0]), SENDERS[0], shift) for shift in (0, 1)}
    for shift, spec in specs.items():
        path = output / f'expectations-layout-{shift}.json'
        write_json(path, spec)
        if file_sha256(path) != STATE_ARCHIVES[shift]:
            raise HarnessError('independent state expectations changed')
    write_json(output / 'packed-expectations.json', specs[0]['packedExpectations'])
    if file_sha256(output / 'packed-expectations.json') != PACKED_ARCHIVE_SHA256:
        raise HarnessError('independent packed expectations changed')
    results = {}
    source = FIXTURE.read_text()
    for name, text in source_variants(source).items():
        directory = output / name
        path, built = compile_variant(directory, text, solc)
        spec = read_prefix(specs[int(name == 'shifted-layout')])
        write_json(directory / 'read-prefix.json', spec)
        result = replay_expected(spec, {'source': source_adapter(directory / 'source', built, spec)},
                                 required_routes=('source',))
        write_json(directory / 'execution.json', result)
        mutant = name in ('wrong-mapping-base', 'short-hash')
        require_source(result, mutant)
        results[name] = {'sourceSha256': file_sha256(path), 'sourceReads': 6,
                         'mismatches': result['mismatches'], 'combinedThreeRouteAgreement': False}
        if mutant:
            continue
        admission = observe(directory, path.name, CONTRACT, READ)
        require_rejection(admission, COMPOSITION_REJECTION)
        results[name]['admission'] = admission
        if name == 'original':
            digest = run_root(directory / 'digest', path.name, CONTRACT, DIGEST,
                packed_cases('digest', spec['packedExpectations']), built, solc, compiler, False)
            if digest['status'] != 'admitted' or digest['execution']['status'] != 'executed':
                raise HarnessError('required full-cleanup hash control did not execute')
            write_json(directory / 'digest-result.json', digest)
            key_spec = key_read_inputs(spec)
            write_json(directory / 'key-inputs.json', key_spec['transactions'])
            driver, snapshot = prepare_model(directory / 'key-model', path, CONTRACT,
                                             [KEY_READ], compiler)
            compiled = compile_generated(directory / 'key-model', snapshot, solc)
            key_result = run_routes(directory / 'key-routes', key_spec, path, built, driver, compiled)
            require_outcome(key_result)
            results[name]['controls'] = {'hashThreeRouteCases': len(spec['packedExpectations']),
                                        'suppliedKeyThreeRouteReads': 6}
    original = results['original']['admission']
    renamed = results['renamed']['admission']
    for key in ('node', 'reason', 'closure'):
        if original[key] != renamed[key].replace('deriveKey', 'packedKey').replace('findRecord', 'locate'):
            raise HarnessError('helper spelling changed the composition rejection')
    for name, text, signature, reason in rejected_sources(source):
        directory = output / name
        path, _ = compile_variant(directory, text, solc)
        observation = observe(directory, path.name, CONTRACT, signature)
        require_rejection(observation, reason)
        results[name] = {'sourceSha256': file_sha256(path), 'admission': observation}
    identity.verify()
    write_json(output / 'implementation.json', identity.manifest)
    write_json(output / 'manifest.json', {
        'verityHead': identity.manifest['revision'],
        'worktreeStatus': command(['git', 'status', '--porcelain'], cwd=ROOT),
        'compiler': compiler, 'settings': SETTINGS, 'fork': 'cancun',
        'stateArchivesSha256': STATE_ARCHIVES, 'packedArchiveSha256': PACKED_ARCHIVE_SHA256,
        'readProjection': 'unchanged first six transactions and observations from each full archive',
        'scope': 'full-cleanup read-only preparation; no importer admission change',
        'missingCombinedRoutes': ['model', 'compiled'],
        'limits': ['separate controls do not establish composition',
                   'no tail-only cleanup, write/log, constructor, gas or whole-world equivalence',
                   'pinned downstream wrapper and compiler correspondence remain pending'],
    })
    write_json(output / 'results.json', {'preparationPassed': True,
        'combinedThreeRouteAgreement': False, 'variants': results})
    print('3 source read variants, 2 source mutants, 9 located rejections; '
          '54 hash cases and 6 supplied-key reads pass three routes; composition remains blocked')
    return 1 if require_composition else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    parser.add_argument('--require-composition', action='store_true')
    args = parser.parse_args()
    try:
        return run(args.output, prepared=args.prepared, require_composition=args.require_composition)
    except (HarnessError, OSError, ValueError) as exc:
        print(json.dumps({'infrastructureFailure': str(exc)}))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
