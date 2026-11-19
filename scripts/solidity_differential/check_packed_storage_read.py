"""Check packed-hash storage reads after full and partial cleanup on three execution routes."""
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


def partial_cleanup(source):
    clears = '            mstore(base, 0)\n            mstore(add(base, 32), 0)\n'
    if source.count(clears) != 1:
        raise HarnessError('full-cleanup source anchor changed')
    return source.replace(clears, '')


def source_variants(source):
    variants = {
        'original': source,
        'renamed': source.replace('packedKey', 'deriveKey').replace('locate', 'findRecord'),
        'shifted-layout': source.replace('uint256 private outerBefore;',
                                       'uint256 private extra; uint256 private outerBefore;'),
        'caller-buffer-read': source.replace(
            'Record storage row = locate(account, left, right, salt);',
            'Record storage row = locate(account, left, right, salt);\n'
            '        uint256 observed; assembly ("memory-safe") {\n'
            '            let p := mload(0x40)\n'
            '            observed := or(mload(p), or(mload(add(p, 32)), mload(add(p, 64))))\n'
            '        } require(observed == 0);'),
        'wrong-mapping-base': source.replace('uint256 private outerBefore;',
                                            'uint256[2] private outerBefore;'),
        'short-hash': source.replace('keccak256(add(base, 12), 58)',
                                    'keccak256(add(base, 12), 57)'),
        # Former rejection control: preserve the exact source defect and now
        # require every executed route to detect its unexpected state change.
        'storage-write': source.replace(
            'Record storage row = locate(account, left, right, salt);',
            'Record storage row = locate(account, left, right, salt);\n'
            '        row.accumulator = 1;').replace('external view returns', 'external returns'),
    }
    return {**variants, 'partial-cleanup': partial_cleanup(source),
            'partial-cleanup-shifted': partial_cleanup(variants['shifted-layout']),
            'partial-cleanup-wrong-base': partial_cleanup(variants['wrong-mapping-base'])}


def rejected_sources(source):
    tail = partial_cleanup(source)
    lookup = 'return bucket.records[packedKey(account, left, right, salt)];'
    if tail.count(lookup) != 1:
        raise HarnessError('mapping key source anchor changed')
    yield ('partial-cleanup-unrelated-key', tail.replace(lookup,
           'bytes32 key = packedKey(account, left, right, salt); key = salt; return bucket.records[key];'),
           READ, 'bounded memory leaves dirty scalar bytes visible after assembly')
    yield ('partial-cleanup-caller-read', partial_cleanup(source_variants(source)['caller-buffer-read']),
           READ, 'bounded memory leaves dirty scalar bytes visible after assembly')
    for name, signature, before, after, reason in (
        ('dirty-hash', DIGEST, 'keccak256(add(base, 12), 58)', 'keccak256(base, 58)',
         'bounded memory hash observes dirty scalar bytes'),
        ('dirty-read', DIGEST, 'keccak256(add(base, 12), 58)', 'mload(base)',
         'bounded memory observes dirty scalar bits'),
        ('unknown-cleanup-alias', DIGEST, 'mstore(base, 0)', 'mstore(128, 0)',
         'bounded memory cannot establish disjointness from dirty bytes'),
    ):
        if source.count(before) != 1:
            raise HarnessError('rejection source anchor changed')
        yield name, source.replace(before, after), signature, reason
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
    caller = 'Record storage row = locate(account, left, right, salt);'
    for name, statements, reason in (
        ('memory-after-write', 'row.accumulator = 1; uint256 observed; '
         'assembly ("memory-safe") { let p := mload(0x40) observed := mload(p) } '
         'row.accumulator = observed;',
         'bounded memory storage effects require a memory-independent successful suffix'),
        ('storage-pointer', 'uint256 pointer = row.accumulator; '
         'assembly { mstore(pointer, 0) }',
         'bounded memory requires nonwrapping addresses in [128, 2^32), or word 0x40'),
        ('storage-free-pointer', 'uint256 pointer = row.accumulator; '
         'assembly { mstore(0x40, pointer) }',
         'bounded memory requires a bounded free pointer'),
        ('unregistered-scratch', 'bytes32 scratch; assembly { '
         'mstore(0, salt) mstore(32, salt) let _verity_slice_tmp_0 := keccak256(0, 64) '
         'scratch := _verity_slice_tmp_0 }',
         COMPOSITION_REJECTION),
    ):
        text = source.replace(caller, caller + '\n        ' + statements)
        if name == 'memory-after-write':
            text = text.replace('external view returns', 'external returns')
        if name == 'unregistered-scratch':
            text = text.replace('return (row.count, row.accumulator, row.checkpoint);\n    }\n}',
                                'return (row.count, row.accumulator, uint256(scratch));\n    }\n}')
        yield name, text, READ, reason


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


def require_source(result, mutant=False, *, mutation_fields=('data',)):
    if result.get('routes') != ['source'] or set(result.get('mismatches', {})) != {'source'}:
        raise HarnessError('missing actual source execution')
    rows = result['mismatches']['source']
    if (bool(rows) != mutant or any(row['fields'] != list(mutation_fields) for row in rows)):
        raise HarnessError('source read or mandatory return-data mutation evidence failed')


def require_combined(result, mutant=False, *, mutation_fields=('data',)):
    """All routes must execute; source defects must remain observable in every route."""
    if not mutant:
        require_outcome(result)
        return
    routes = ['source', 'model', 'compiled']
    if (result.get('routes') != routes or set(result.get('mismatches', {})) != set(routes)
            or result.get('divergences') != []):
        raise HarnessError('missing or divergent combined mutation execution')
    for route in routes:
        require_source({'routes': ['source'], 'mismatches': {'source': result['mismatches'][route]}},
                       mutant=True, mutation_fields=mutation_fields)


def require_record_slots(result, spec):
    """Each call touches its own count word, plus the two other fields when returning the record."""
    slots = {tuple(int(n) % 2**256 for n in spec['packedExpectations'][i]['values']): int(slot, 16)
             for i, slot in zip(spec['keyIndices'], spec['recordSlots'], strict=True)}
    for stage in ('discovery', 'observations'):
        for route in ('source', 'model', 'compiled'):
            rows = result[stage][route]
            for tx, want, row in zip(spec['transactions'], spec['expected'], rows, strict=True):
                slot = slots[tuple(tx['args'][:4])]
                expected = {(tx['target'], '0x' + word(slot + offset).hex())
                            for offset in range(1 if want['status'] == 'revert' else 3)}
                if row['id'] != tx['id'] or set(map(tuple, row['touched'])) != expected:
                    raise HarnessError(f'{stage} {route} {tx["id"]}: wrong physical record slots')


def run_record_reads(directory, spec, path, contract, built, solc, compiler):
    driver, snapshot = prepare_model(directory / 'combined-model', path, contract, [READ], compiler)
    compiled = compile_generated(directory / 'combined-model', snapshot, solc)
    return run_routes(directory / 'combined-routes', spec, path, built, driver, compiled)


def run_digest_control(directory, path, expected, built, solc, compiler):
    digest = run_root(directory / 'digest', path.name, CONTRACT, DIGEST,
                      packed_cases('digest', expected), built, solc, compiler, False)
    if digest['status'] != 'admitted' or digest['execution']['status'] != 'executed':
        raise HarnessError('required three-route digest control did not execute')
    write_json(directory / 'digest-result.json', digest)


def run(output, *, prepared=False):
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
        spec = read_prefix(specs[int(name in ('shifted-layout', 'partial-cleanup-shifted'))])
        write_json(directory / 'read-prefix.json', spec)
        result = replay_expected(spec, {'source': source_adapter(directory / 'source', built, spec)},
                                 required_routes=('source',))
        write_json(directory / 'execution.json', result)
        mutant = name in ('wrong-mapping-base', 'partial-cleanup-wrong-base', 'short-hash', 'storage-write')
        mutation_fields = ('data', 'storage') if name == 'storage-write' else ('data',)
        require_source(result, mutant, mutation_fields=mutation_fields)
        results[name] = {'sourceSha256': file_sha256(path), 'sourceReads': 6,
                         'mismatches': result['mismatches'], 'combinedThreeRouteAgreement': False}
        combined = run_record_reads(directory, spec, path, CONTRACT, built, solc, compiler)
        require_combined(combined, mutant, mutation_fields=mutation_fields)
        if not mutant:
            require_record_slots(combined, spec)
        results[name].update({'combinedThreeRouteAgreement': not mutant,
                              'mutationDetectedOnAllRoutes': mutant,
                              'mismatches': combined['mismatches']})
        if name in ('original', 'partial-cleanup'):
            run_digest_control(directory, path, spec['packedExpectations'], built, solc, compiler)
            results[name]['controls'] = {'hashThreeRouteCases': len(spec['packedExpectations'])}
        if name == 'original':
            key_spec = key_read_inputs(spec)
            write_json(directory / 'key-inputs.json', key_spec['transactions'])
            driver, snapshot = prepare_model(directory / 'key-model', path, CONTRACT,
                                             [KEY_READ], compiler)
            compiled = compile_generated(directory / 'key-model', snapshot, solc)
            key_result = run_routes(directory / 'key-routes', key_spec, path, built, driver, compiled)
            require_outcome(key_result)
            results[name]['controls']['suppliedKeyThreeRouteReads'] = 6
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
        'scope': 'full and partial cleanup before packed-key storage reads',
        'missingCombinedRoutes': [],
        'limits': ['execution regression evidence is not an importer correspondence theorem',
                   'no tail-only writes, logs, rollback, constructor or gas equivalence',
                   'pinned downstream wrapper and compiler correspondence remain pending'],
    })
    write_json(output / 'results.json', {'combinedThreeRouteAgreement': True, 'variants': results})
    print('Packed-key reads and controls agree across source, Denote and generated EVM; '
          'source defects remain detectable and excluded roots remain rejected')
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    parser.add_argument('--require-composition', action='store_true',
                        help='compatibility flag: composition is now always required')
    args = parser.parse_args()
    try:
        return run(args.output, prepared=args.prepared)
    except (HarnessError, OSError, ValueError) as exc:
        print(json.dumps({'infrastructureFailure': str(exc)}))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
