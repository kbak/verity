"""Real three-route storage control; the unchanged packed-reference milestone remains blocked."""
import argparse
import copy
import json
from pathlib import Path
import shutil
import sys

from keccak256 import selector
from setup_solc_import import file_sha256
from .check_packed_memory_hash import SETTINGS, word
from .check_packed_memory_hash_import import observe
from .check_storage_reference import source_adapter
from .denote import SequenceAdapter as Denote
from .engine import HarnessError, ROOT, command, solc_compile, write_json
from .hash_execution import compile_generated, pinned_compiler
from .identity import ImplementationIdentity
from .pinned_sequence import SENDERS, create_address
from .stateful import ROUTES, compare_sequences
from .storage_reference_oracle import (
    PACKED_ARCHIVE_SHA256, SIGNATURES as PACKED_SIGNATURES, replay_expected, specification,
)
from .storage_sequence_execution import prepare_model

FIXTURE = ROOT / 'Contracts/SolidityImportSmoke/StorageReferenceControl.sol'
PACKED_FIXTURE = ROOT / 'Contracts/SolidityImportSmoke/PackedStorageReference.sol'
CONTRACT = 'StorageReferenceControl'
SIGNATURES = {name: signature.replace('address,int24,int24,bytes32', 'bytes32')
              for name, signature in PACKED_SIGNATURES.items()}
STATE_ARCHIVES = {
    0: '308a405f0be29c1a59fc0f5d2603b0a6286df26d8ffc90f7a2f2c23e3b3d7ab7',
    1: '41397c6193b3b2c60ee5b0053e2014fefb6e6cf054d36bff4e272529b1f9c058',
}


def control_inputs(spec):
    """Change only control calldata: pass independently specified keys instead of computing them.

    Initial storage, complete expected observations, transaction identities and call environments
    remain byte-for-byte equal to the packed fixture's specification. This is not a packed hash test.
    """
    result = copy.deepcopy(spec)
    keys = {tuple(int(n) % 2**256 for n in row['values']): int(row['hash'], 16)
            for row in spec['packedExpectations']}
    for original, tx in zip(spec['transactions'], result['transactions']):
        name, args = tx['function'], tx['args']
        signature = PACKED_SIGNATURES[name]
        if (len(args) != (4 if name == 'read' else 5)
                or tx['data'] != selector(signature) + b''.join(word(n) for n in args).hex()
                or tuple(args[:4]) not in keys):
            raise HarnessError('packed specification input drift')
        tx['args'] = [keys[tuple(args[:4])], *args[4:]]
        tx['data'] = selector(SIGNATURES[name]) + b''.join(word(n) for n in tx['args']).hex()
        if any(tx[k] != original[k] for k in original if k not in ('args', 'data')):
            raise HarnessError('control input conversion changed the call environment')
    return result


def build_source(directory, source, solc):
    directory.mkdir(parents=True, exist_ok=False)
    path = directory / FIXTURE.name
    path.write_text(source)
    request = {'language': 'Solidity', 'sources': {path.name: {'content': source}},
               'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
                   'abi', 'storageLayout', 'evm.methodIdentifiers',
                   'evm.bytecode.object', 'evm.deployedBytecode.object']}}}}
    result = solc_compile(request, directory, directory / 'source', solc=solc)
    built = result['contracts'][path.name][CONTRACT]
    if built['evm']['methodIdentifiers'] != {s: selector(s)[2:] for s in SIGNATURES.values()}:
        raise HarnessError('storage control source signatures/selectors differ')
    if any(item['type'] == 'constructor' for item in built['abi']):
        raise HarnessError('storage control must have no source constructor')
    return path, built


def run_routes(directory, spec, source, built, driver, compiled):
    identity = ImplementationIdentity(driver, extra_inputs=(source,))
    adapters = {
        'source': source_adapter(directory / 'source', built, spec),
        'model': Denote(directory / 'model', driver, spec['target'], spec['initialStorage'],
                        identity=identity, account_nonce=1,
                        lean_command=(sys.executable, '-m',
                                      'solidity_differential.storage_sequence_execution')),
        'compiled': source_adapter(directory / 'compiled', compiled, spec),
    }
    result = replay_expected(spec, adapters, required_routes=ROUTES)
    identity.verify()
    result['divergences'] = compare_sequences([tx['id'] for tx in spec['transactions']],
                                              result['observations'])
    write_json(directory / 'implementation.json', identity.manifest)
    write_json(directory / 'execution.json', result)
    return result


def require_outcome(result, mutated_route=None):
    """A real event-deletion mutant must affect only its executed route's log observations."""
    if set(result.get('mismatches', {})) != set(ROUTES) or result.get('routes') != list(ROUTES):
        raise HarnessError('missing actual execution route')
    for route, mismatches in result['mismatches'].items():
        if route == mutated_route:
            if not mismatches or any(row['fields'] != ['events'] for row in mismatches):
                raise HarnessError('event-deletion mutant lacks exact executed log evidence')
        elif mismatches:
            raise HarnessError(f'{route}: independent storage expectations failed: {mismatches[:3]}')
    if bool(result['divergences']) != (mutated_route is not None):
        raise HarnessError('route comparison disagrees with independent expectations')


def run(output, *, prepared=False, require_packed_reference=False):
    output = output.resolve()
    if not output.is_relative_to(ROOT):
        raise HarnessError('output must be inside the checkout')
    output.mkdir(parents=True, exist_ok=False)
    head = command(['git', 'rev-parse', 'HEAD'], cwd=ROOT).strip()
    solc, compiler = pinned_compiler()
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.Differential', 'Compiler.SolidityImport.SequenceRunner',
                 '--project-dir', ROOT], cwd=ROOT, timeout=1800, log=output / 'build.log')
    variants = {'original': FIXTURE.read_text(),
                'renamed': FIXTURE.read_text().replace('locate', 'selectRecord'),
                'shifted-layout': FIXTURE.read_text().replace('uint256 private outerBefore;',
                    'uint256 private extra; uint256 private outerBefore;')}
    specs = {i: specification(create_address(SENDERS[0]), SENDERS[0], i) for i in (0, 1)}
    for shift, spec in specs.items():
        path = output / f'expectations-layout-{shift}.json'
        write_json(path, spec)
        if file_sha256(path) != STATE_ARCHIVES[shift]:
            raise HarnessError('independent storage expectations changed')
    write_json(output / 'packed-expectations.json', specs[0]['packedExpectations'])
    if file_sha256(output / 'packed-expectations.json') != PACKED_ARCHIVE_SHA256:
        raise HarnessError('independent packed expectations changed')
    results = {}
    for name, text in variants.items():
        directory = output / name
        source, built = build_source(directory, text, solc)
        spec = control_inputs(specs[int(name == 'shifted-layout')])
        write_json(directory / 'control-inputs.json', spec['transactions'])
        driver, snapshot = prepare_model(directory / 'imported', source, CONTRACT,
                                         list(SIGNATURES.values()), compiler)
        compiled = compile_generated(directory / 'imported', snapshot, solc)
        result = run_routes(directory / 'baseline', spec, source, built, driver, compiled)
        require_outcome(result)
        results[name] = {'controlThreeRouteAgreement': True, 'transactions': len(spec['transactions']),
                         'sourceDigest': snapshot['digest'], 'compilerProof': snapshot['compilerProof']}
        if name == 'original':
            bad_driver, bad_snapshot = prepare_model(directory / 'drop-events', source, CONTRACT,
                list(SIGNATURES.values()), compiler, mutation='drop-events')
            bad_compiled = compile_generated(directory / 'drop-events', bad_snapshot, solc)
            for route in ('model', 'compiled'):
                result = run_routes(directory / f'{route}-drop-events', spec, source, built,
                    bad_driver if route == 'model' else driver,
                    bad_compiled if route == 'compiled' else compiled)
                require_outcome(result, route)
                results[f'{route}-drop-events'] = {'detected': True,
                    'mismatches': result['mismatches'], 'routes': result['routes']}
    packed_dir = output / 'packed-admission'
    packed_dir.mkdir()
    shutil.copy(PACKED_FIXTURE, packed_dir)
    imports = {root: observe(packed_dir, PACKED_FIXTURE.name, 'PackedStorageReference', signature)
               for root, signature in PACKED_SIGNATURES.items()}
    if command(['git', 'rev-parse', 'HEAD'], cwd=ROOT).strip() != head:
        raise HarnessError('Git head changed during storage campaign')
    write_json(output / 'manifest.json', {
        'verityHead': head, 'worktreeStatus': command(['git', 'status', '--porcelain'], cwd=ROOT),
        'compiler': compiler, 'settings': SETTINGS, 'targetFork': 'cancun',
        'files': {str(p.relative_to(ROOT)): file_sha256(p) for p in (
            FIXTURE, PACKED_FIXTURE, Path(__file__),
            Path(__file__).with_name('storage_reference_oracle.py'),
            Path(__file__).with_name('storage_sequence_execution.py'))},
        'expectationsSha256': STATE_ARCHIVES, 'packedExpectationsSha256': PACKED_ARCHIVE_SHA256,
        'controlScope': 'precomputed independent keys; packed hash execution is not part of the control',
        'observations': 'persistent storage, return/revert bytes and logs after every transaction',
        'limits': ['explicit initial world, not constructor equivalence',
                   'no gas/resource, balance/nonce, arbitrary memory or compiler correspondence proof',
                   'packed-reference sequence and pinned downstream wrapper remain pending'],
    })
    write_json(output / 'results.json', {'controlsPassed': True, 'controls': results,
        'packedImports': imports, 'packedReferenceThreeRouteAgreement': False})
    print('3 storage controls: 29 transactions each agree across source/Denote/generated EVM; '
          'both executed route mutants detected; packed-reference milestone remains closed')
    return 1 if require_packed_reference else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    parser.add_argument('--require-packed-reference', action='store_true')
    args = parser.parse_args()
    try:
        return run(args.output, prepared=args.prepared,
                   require_packed_reference=args.require_packed_reference)
    except (HarnessError, OSError, ValueError) as exc:
        print(json.dumps({'infrastructureFailure': str(exc)}))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
