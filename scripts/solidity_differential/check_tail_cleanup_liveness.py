"""Execute the saved-hash caller on three routes and check the remaining caller boundaries."""
import argparse
import json
from pathlib import Path

from setup_solc_import import file_sha256
from .check_packed_memory_hash import SETTINGS, SHIFTS
from .check_packed_memory_hash_import import observe
from .check_packed_memory_hash_routes import case, run_root
from .check_packed_storage_read import require_rejection
from .check_storage_reference import compile_variant as compile_storage
from .check_storage_reference_routes import PACKED_FIXTURE, STATE_ARCHIVES
from .engine import HarnessError, ROOT, command, write_json
from .hash_execution import (
    compile_source, execute_evm, pinned_compiler, validate_cases, validate_observations, verify_abi,
)
from .identity import ImplementationIdentity
from .pinned_sequence import SENDERS, create_address
from .storage_reference_oracle import PACKED_ARCHIVE_SHA256, SIGNATURES, specification

FIXTURE = ROOT / 'Contracts/SolidityImportSmoke/TailCleanupCaller.sol'
CONTRACT = 'TailCleanupCaller'
SIGNATURE = 'probe(address,int24,int24,bytes32,uint256,uint256,uint256)'
REJECTION = 'bounded memory leaves dirty scalar bytes visible after assembly'
POISONS = (0, 1, 2**96 - 1)
CONTINUATIONS = {
    'saved-hash': '',
    'overwrite-before-read': 'mstore(base, 0)\nresult := xor(result, shr(160, mload(base)))',
    'disjoint-tail-read': 'result := xor(result, mload(add(base, 64)))',
    'known-alias': 'let alias := base\nmstore(alias, 0)\n'
                   'result := xor(result, shr(160, mload(base)))',
    'read-before-overwrite': 'let captured := shr(160, mload(base))\nmstore(base, 0)\n'
                             'result := xor(result, captured)',
    'insufficient-overwrite': 'mstore(add(base, 12), 0)\n'
                              'result := xor(result, shr(160, mload(base)))',
    'overlapping-byte-read': 'result := xor(result, byte(0, mload(add(base, 11))))',
    'parameter-alias': 'mstore(add(base, cleanupOffset), 0)\n'
                       'result := xor(result, shr(160, mload(base)))',
}
# These two continuations reach an unsupported operation while lowering the caller itself.
CALLER_REJECTIONS = {
    'overlapping-byte-read': 'unsupported bounded-memory word operation',
    'parameter-alias': 'unsupported bounded-memory address expression',
}


def source_variants(source):
    anchor = '            // CALLER_CONTINUATION'
    if source.count(anchor) != 1:
        raise HarnessError('caller continuation anchor changed')
    return {name: source.replace(anchor, '\n'.join('            ' + line
                for line in code.splitlines())) for name, code in CONTINUATIONS.items()}


def caller_cases(expected, name):
    """Extend inputs only; every outcome is still the unchanged independent packed hash."""
    if name not in CONTINUATIONS:
        raise HarnessError('unknown caller continuation')
    return [case(f'{index}:{shift}:{poison}:{offset}', SIGNATURE,
                 [*map(int, row['values']), shift, poison, offset], row['hash'])
            for index, row in enumerate(expected) for shift in SHIFTS for poison in POISONS
            for offset in ((0, 32) if name == 'parameter-alias' else (0,))]


def required_mismatches(cases, name):
    """Require sensitivity, not replacement expected outputs, for deliberately exposed bits."""
    if name not in CONTINUATIONS:
        raise HarnessError('unknown caller continuation')
    result = []
    for row in cases:
        poison, offset = map(int, row['args'][-2:])
        exposed = (name in ('read-before-overwrite', 'insufficient-overwrite') and poison != 0
                   or name == 'overlapping-byte-read' and poison & 255 != 0
                   or name == 'parameter-alias' and poison != 0 and offset == 32)
        if exposed:
            result.append(row['id'])
    return result


def check_observations(rows, cases, name):
    validate_cases(SIGNATURE, cases)
    validate_observations(rows, cases)
    mismatches = [row['id'] for row, want in zip(rows, cases) if row['data'] != want['expected']]
    if mismatches != required_mismatches(cases, name):
        raise HarnessError('caller exposure or mandatory perturbation detection failed')
    return {'calls': len(cases), 'mismatches': mismatches}


def archive_expectations(output):
    specs = {shift: specification(create_address(SENDERS[0]), SENDERS[0], shift) for shift in (0, 1)}
    for shift, spec in specs.items():
        path = output / f'expectations-layout-{shift}.json'
        write_json(path, spec)
        if file_sha256(path) != STATE_ARCHIVES[shift]:
            raise HarnessError('independent state expectations changed')
    path = output / 'packed-expectations.json'
    write_json(path, specs[0]['packedExpectations'])
    if file_sha256(path) != PACKED_ARCHIVE_SHA256:
        raise HarnessError('independent packed expectations changed')
    return specs[0]['packedExpectations']


def require_saved_routes(report, count):
    execution = report['execution']
    routes = execution.get('routes', {})
    if (report['status'] != 'admitted' or execution['status'] != 'executed'
            or set(routes) != {'source', 'denote', 'generatedEvm'}
            or any(row != {'calls': count, 'mismatches': [], 'hashMismatches': []}
                   for row in routes.values())):
        raise HarnessError('saved hash requires all three routes to match every frozen return')
    return routes


def check_saved_return_boundaries(output, source):
    restore = 'mstore(0x40, original)'
    if source.count(restore) != 1:
        raise HarnessError('caller restore site changed')
    controls = {
        'reassigned-return': 'result := 0\n            ' + restore,
        'unrestored-pointer': '',
        'different-pointer': 'mstore(0x40, add(original, 32))',
    }
    results = {}
    for name, replacement in controls.items():
        directory = output / name
        directory.mkdir()
        (directory / FIXTURE.name).write_text(source.replace(restore, replacement))
        observation = observe(directory, FIXTURE.name, CONTRACT, SIGNATURE)
        require_rejection(observation, REJECTION)
        results[name] = observation
    return results


def preparation_exit(require_composition):
    # More general observing callers and the original storage roots still lack composition.
    return 1 if require_composition else 0


def run(output, *, prepared=False, require_composition=False):
    output = output.resolve()
    if not output.is_relative_to(ROOT):
        raise HarnessError('output must be inside the checkout')
    output.mkdir(parents=True, exist_ok=False)
    solc, compiler = pinned_compiler()
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.Differential', '--project-dir', ROOT], cwd=ROOT,
                timeout=1800, log=output / 'build.log')
    identity = ImplementationIdentity(FIXTURE, extra_inputs=(PACKED_FIXTURE,))
    expected = archive_expectations(output)
    results = {}
    for name, source in source_variants(FIXTURE.read_text()).items():
        directory = output / name
        directory.mkdir()
        path = directory / FIXTURE.name
        path.write_text(source)
        built = compile_source(directory, path.name, CONTRACT, solc)
        cases = caller_cases(expected, name)
        if name == 'saved-hash':
            report = run_root(directory / 'routes', path.name, CONTRACT, SIGNATURE, cases,
                              built, solc, compiler, False)
            routes = require_saved_routes(report, len(cases))
            results[name] = {'sourceSha256': file_sha256(path), 'execution': routes['source'],
                             'threeRouteExecution': report['execution'],
                             'admission': {'status': report['status'],
                                           'sourceDigest': report['sourceDigest']}}
            write_json(directory / 'result.json', results[name])
            continue
        validate_cases(SIGNATURE, cases)
        verify_abi(built, SIGNATURE, cases)
        write_json(directory / 'cases.json', cases)
        rows, _ = execute_evm(directory / 'source-evm', built, cases)
        execution = check_observations(rows, cases, name)
        admission = observe(directory, path.name, CONTRACT, SIGNATURE)
        require_rejection(admission, CALLER_REJECTIONS.get(name, REJECTION))
        results[name] = {'sourceSha256': file_sha256(path), 'execution': execution,
                         'admission': admission}
        write_json(directory / 'result.json', results[name])
    directory = output / 'original-storage'
    directory.mkdir()
    compile_storage(directory, PACKED_FIXTURE.read_text(), solc)
    original = {}
    for name, signature in SIGNATURES.items():
        observation = observe(directory, PACKED_FIXTURE.name, 'PackedStorageReference', signature)
        require_rejection(observation, REJECTION)
        original[name] = observation
    boundaries = check_saved_return_boundaries(output, FIXTURE.read_text())
    identity.verify()
    write_json(output / 'implementation.json', identity.manifest)
    write_json(output / 'manifest.json', {
        'verityHead': identity.manifest['revision'],
        'worktreeStatus': command(['git', 'status', '--porcelain'], cwd=ROOT),
        'compiler': compiler, 'settings': SETTINGS, 'fork': 'cancun',
        'stateArchivesSha256': STATE_ARCHIVES, 'packedArchiveSha256': PACKED_ARCHIVE_SHA256,
        'scope': 'saved hash on three routes; source perturbations for observing callers',
        'savedHashRoutes': ['source', 'denote', 'generatedEvm'],
        'limits': ['state archives retained unchanged, not executed by this stateless campaign',
                   'no universal liveness, storage sequence, gas or compiler correspondence claim'],
    })
    write_json(output / 'results.json', {'preparationPassed': True,
        'savedHashThreeRouteAgreement': True, 'tailThreeRouteAgreement': False,
        'variants': results, 'savedReturnBoundaries': boundaries, 'originalStorage': original})
    calls = sum(row['execution']['calls'] for row in results.values())
    print(f'{calls} source calls; saved hash agrees on three routes; '
          'observing callers and storage roots remain blocked')
    return preparation_exit(require_composition)


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
