"""Require successful full-cleanup storage updates and logs on three real routes."""
import argparse
import copy
import json
from pathlib import Path

from setup_solc_import import file_sha256
from .check_packed_memory_hash_import import observe
from .check_packed_storage_read import require_rejection
from .check_storage_reference import CONTRACT, FIXTURE, compile_variant, variants
from .check_storage_reference_routes import STATE_ARCHIVES, require_outcome, run_routes
from .engine import HarnessError, ROOT, command, write_json
from .hash_execution import compile_generated, pinned_compiler
from .identity import ImplementationIdentity
from .pinned_sequence import SENDERS, create_address
from .stateful import ROUTES
from .storage_reference_oracle import PACKED_ARCHIVE_SHA256, SIGNATURES, specification
from .storage_sequence_execution import prepare_model

SUCCESS_ROOTS = ('read', 'setCount', 'setAccumulator', 'setCheckpoint')
EFFECT_REJECTION = ('bounded memory storage effects require a memory-independent successful suffix')
SOURCE_MUTANTS = {'wrong-mapping-base': 'storage', 'wrong-field': 'storage', 'drop-event': 'events'}


def successful_prefix(spec):
    """Keep complete original rows up to, but not including, the first explicit revert."""
    result = copy.deepcopy(spec)
    operations = ('read',) * 6 + ('setCount', 'setAccumulator', 'setCheckpoint', 'setCount')
    end = len(operations)
    if (len(spec['transactions']) != len(spec['expected'])
            or len(spec['transactions']) <= end
            or spec['transactions'][end]['function'] != 'writeThenRevert'
            or spec['expected'][end]['status'] != 'revert'
            or tuple(tx['function'] for tx in spec['transactions'][:end]) != operations
            or any(tx['id'] != want['id'] or want['status'] != 'ok'
                   or len(want['events']) != int(tx['function'] != 'read')
                   for tx, want in zip(spec['transactions'][:end], spec['expected'][:end]))):
        raise HarnessError('independent successful-update prefix changed')
    result['transactions'] = result['transactions'][:end]
    result['expected'] = result['expected'][:end]
    return result


def source_variants(source):
    """Reuse the existing full-cleanup control and source defects, without editing the fixture."""
    full = variants(source)['full-cleanup']
    choices = variants(full)
    return {name: choices[name] for name in ('original', 'renamed', 'shifted-layout',
                                            *SOURCE_MUTANTS)}


def require_source_mutant(result, required_field):
    """A source defect must execute and be detected independently on every route."""
    if (result.get('routes') != list(ROUTES) or result.get('divergences') != []
            or set(result.get('mismatches', {})) != set(ROUTES)):
        raise HarnessError('missing or divergent source-mutant routes')
    allowed = {'events'} if required_field == 'events' else {'data', 'storage'}
    for rows in result['mismatches'].values():
        if (not any(required_field in row['fields'] for row in rows)
                or any(not row['fields'] or not set(row['fields']) <= allowed for row in rows)):
            raise HarnessError('source mutation needs semantic evidence, not execution failure')


def rejected_sources(source):
    full = source_variants(source)['original']
    yield 'write-then-revert', full, SIGNATURES['writeThenRevert'], EFFECT_REJECTION
    anchor = '        emit Changed(0, next);'
    for name, text in (
        ('read-after-log', anchor + '\n        uint256 observed; assembly ("memory-safe") { '
                           'let p := mload(0x40) observed := mload(p) }\n'
                           '        row.accumulator = observed;'),
        ('hash-after-log', anchor + '\n        bytes32 observed; assembly ("memory-safe") { '
                           'let p := mload(0x40) observed := keccak256(p, 32) }\n'
                           '        row.accumulator = uint256(observed);'),
        ('guard-after-write', '        require(next != 0);\n' + anchor),
        ('lookup-after-log', anchor + '\n        Record storage again = '
                             'locate(account, left, right, salt);\n'
                             '        row.accumulator = again.checkpoint;'),
    ):
        yield name, full.replace(anchor, text, 1), SIGNATURES['setCount'], EFFECT_REJECTION
    before_hash = full.replace('        Record storage row = locate(account, left, right, salt);',
        '        emit Changed(0, next);\n'
        '        Record storage row = locate(account, left, right, salt);', 1)
    # The first occurrence belongs to the view root: make that separate root stateful.
    before_hash = before_hash.replace('emit Changed(0, next);', 'emit Changed(0, 0);', 1)
    before_hash = before_hash.replace('external view returns', 'external returns', 1)
    yield 'log-before-hash', before_hash, SIGNATURES['read'], EFFECT_REJECTION
    oversized = full.replace('let base := mload(0x40)',
                             f'mstore(0x40, {2**32 - 96})\n            let base := mload(0x40)')
    oversized = oversized.replace('Changed', 'ScalarChange' + 'X' * 120)
    yield 'event-footprint-overflow', oversized, SIGNATURES['setCount'], (
        'bounded memory event encoding requires a bounded free pointer')


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
    path = output / 'packed-expectations.json'
    write_json(path, specs[0]['packedExpectations'])
    if file_sha256(path) != PACKED_ARCHIVE_SHA256:
        raise HarnessError('independent packed expectations changed')
    results = {}
    signatures = [SIGNATURES[name] for name in SUCCESS_ROOTS]
    for name, source in source_variants(FIXTURE.read_text()).items():
        directory = output / name
        directory.mkdir()
        built = compile_variant(directory, source, solc)
        path = directory / FIXTURE.name
        spec = successful_prefix(specs[int(name == 'shifted-layout')])
        write_json(directory / 'successful-prefix.json', spec)
        driver, snapshot = prepare_model(directory / 'model', path, CONTRACT, signatures, compiler)
        compiled = compile_generated(directory / 'model', snapshot, solc)
        result = run_routes(directory / 'routes', spec, path, built, driver, compiled)
        if name in SOURCE_MUTANTS:
            require_source_mutant(result, SOURCE_MUTANTS[name])
        else:
            require_outcome(result)
        results[name] = {'mismatches': result['mismatches'],
                         'threeRouteAgreement': name not in SOURCE_MUTANTS,
                         'sourceMutationDetected': name in SOURCE_MUTANTS}
        if name == 'original':
            bad_driver, bad_snapshot = prepare_model(directory / 'drop-events', path, CONTRACT,
                                                     signatures, compiler, mutation='drop-events')
            bad_compiled = compile_generated(directory / 'drop-events', bad_snapshot, solc)
            for route in ('model', 'compiled'):
                bad = run_routes(directory / f'{route}-drop-events', spec, path, built,
                    bad_driver if route == 'model' else driver,
                    bad_compiled if route == 'compiled' else compiled)
                require_outcome(bad, route)
                results[f'{route}-drop-events'] = {'detected': True,
                                                   'mismatches': bad['mismatches']}
    for name, source, signature, reason in rejected_sources(FIXTURE.read_text()):
        directory = output / name
        directory.mkdir()
        compile_variant(directory, source, solc)
        admission = observe(directory, FIXTURE.name, CONTRACT, signature)
        require_rejection(admission, reason)
        results[name] = {'admission': admission}
    identity.verify()
    write_json(output / 'implementation.json', identity.manifest)
    write_json(output / 'results.json', {'successfulUpdatesThreeRouteAgreement': True,
        'variants': results, 'fullStorageSequenceAgreement': False,
        'remaining': ['write-then-revert composition', 'tail-only cleanup', 'pinned downstream wrapper']})
    write_json(output / 'manifest.json', {
        'verityHead': identity.manifest['revision'], 'compiler': compiler, 'fork': 'cancun',
        'stateArchivesSha256': STATE_ARCHIVES, 'packedArchiveSha256': PACKED_ARCHIVE_SHA256,
        'projection': 'unchanged contiguous prefix ending immediately before the first revert',
        'scope': 'full-cleanup successful raw-word updates, scalar logs and scalar returns',
        'limits': ['finite regression evidence, not source/importer or compiler correspondence',
                   'no post-effect source memory, control flow, explicit revert or external call',
                   'no gas/resource, constructor or whole-world equivalence'],
    })
    print('Successful full-cleanup updates and exact logs agree on all three routes; '
          'addressing and event defects detected; excluded continuations rejected')
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    try:
        return run(args.output, prepared=args.prepared)
    except (HarnessError, OSError, ValueError) as exc:
        print(json.dumps({'infrastructureFailure': str(exc)}))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
