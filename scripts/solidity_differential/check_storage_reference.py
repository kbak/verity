"""Prepare storage-reference regressions: real source execution, independent state, import status.

Model and generated-EVM sequence execution are intentionally not supplied in this preparation
slice. Located rejections are archived, never counted as semantic agreement or mutation evidence.
"""
import argparse
import json
from pathlib import Path
import shutil

from keccak256 import selector
from setup_solc_import import file_sha256
from .anvil import SequenceAdapter
from .check_packed_memory_hash import SETTINGS
from .check_packed_memory_hash_import import observe
from .engine import HarnessError, ROOT, command, solc_compile, write_json
from .hash_execution import code_bytes, pinned_compiler
from .pinned_sequence import SENDERS, create_address
from .storage_reference_oracle import (
    PACKED_ARCHIVE_SHA256, SIGNATURES, replay_expected, specification,
)

FIXTURE = ROOT / 'Contracts/SolidityImportSmoke/PackedStorageReference.sol'
CONTRACT = 'PackedStorageReference'
POSITIVE = ('original', 'renamed', 'shifted-layout', 'full-cleanup')
MUTANTS = {'wrong-mapping-base': 'storage', 'wrong-field': 'storage',
           'clobber-padding': 'storage', 'drop-revert': 'status', 'drop-event': 'events'}


def variants(source):
    """Only source changes; mutants always reuse the original state/byte expectations."""
    if source.count('row.count = next;') != 2 or source.count('revert Rejected(next);') != 1:
        raise HarnessError('storage mutation anchors changed')
    return {
        'original': source,
        'renamed': source.replace('packedKey', 'deriveKey').replace('locate', 'findRecord'),
        'shifted-layout': source.replace('uint256 private outerBefore;',
                                       'uint256 private extra; uint256 private outerBefore;'),
        'full-cleanup': source.replace('mstore(add(base, 64), 0)',
            'mstore(base, 0) mstore(add(base, 32), 0) mstore(add(base, 64), 0)'),
        'wrong-mapping-base': source.replace('uint256 private outerBefore;',
                                            'uint256[2] private outerBefore;'),
        'wrong-field': source.replace('row.count = next;', 'row.accumulator = next;', 1),
        'clobber-padding': source.replace('row.count = next;',
                                          'assembly { sstore(row.slot, next) }', 1),
        'drop-revert': source.replace('revert Rejected(next);',
                                      'return (row.count, row.accumulator, row.checkpoint);'),
        'drop-event': source.replace('emit Changed(0, next);',
                                    '', 1),
    }


def compile_variant(directory, source, solc):
    (directory / FIXTURE.name).write_text(source)
    request = {'language': 'Solidity', 'sources': {FIXTURE.name: {'content': source}},
               'settings': {**SETTINGS, 'outputSelection': {'*': {'*': [
                   'abi', 'storageLayout', 'evm.methodIdentifiers',
                   'evm.bytecode.object', 'evm.deployedBytecode.object']}}}}
    result = solc_compile(request, directory, directory / 'source', solc=solc)
    built = result['contracts'][FIXTURE.name][CONTRACT]
    for signature in SIGNATURES.values():
        if built['evm']['methodIdentifiers'].get(signature) != selector(signature)[2:]:
            raise HarnessError('source signature or selector drift')
    if any(item['type'] == 'constructor' for item in built['abi']):
        raise HarnessError('fixture constructor equivalence is outside this preparation')
    return built


def source_adapter(directory, built, spec):
    runtime = '0x' + code_bytes(built, 'deployedBytecode').hex()

    def observer(node, record, ident, slots):
        if (node.provenance['hardfork'] != 'cancun'
                or node.rpc('eth_getCode', spec['target'], 'latest') != runtime):
            raise HarnessError('source runtime or fork differs from pinned deployment')
        return node.observe(record, ident, slots)

    return SequenceAdapter(directory, ['0x' + code_bytes(built, 'bytecode').hex()],
                           spec['initialStorage'], observer=observer, hardfork='cancun')


def run(output, *, prepared=False, require_three_routes=False):
    output = output.resolve()
    if not output.is_relative_to(ROOT):
        raise HarnessError('output must be inside this checkout')
    output.mkdir(parents=True, exist_ok=False)
    solc, compiler = pinned_compiler()
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 '--project-dir', ROOT], cwd=ROOT, timeout=1800, log=output / 'build.log')
    sender, target = SENDERS[0], create_address(SENDERS[0])
    specs = {shift: specification(target, sender, shift) for shift in (0, 1)}
    for shift, spec in specs.items():
        write_json(output / f'expectations-layout-{shift}.json', spec)
    write_json(output / 'packed-expectations.json', specs[0]['packedExpectations'])
    if file_sha256(output / 'packed-expectations.json') != PACKED_ARCHIVE_SHA256:
        raise HarnessError('existing independent packed expectations changed')
    results = {}
    for name, source in variants(FIXTURE.read_text()).items():
        directory = output / name
        directory.mkdir()
        built = compile_variant(directory, source, solc)
        spec = specs[int(name == 'shifted-layout')]
        result = replay_expected(spec, {'source': source_adapter(directory / 'execution', built, spec)},
                                 required_routes=('source',))
        write_json(directory / 'execution.json', result)
        mismatches = result['mismatches']['source']
        if name in POSITIVE and mismatches:
            raise HarnessError(f'{name}: independent expected state differs: {mismatches[:3]}')
        if name in MUTANTS and not any(MUTANTS[name] in row['fields'] for row in mismatches):
            raise HarnessError(f'{name}: valid source mutant escaped independent expectations')
        imports = ({root: observe(directory, FIXTURE.name, CONTRACT, signature)
                    for root, signature in SIGNATURES.items()} if name in POSITIVE else {})
        results[name] = {'callsPerReplay': len(spec['transactions']),
                         'sourceExpectationsPassed': not mismatches, 'mismatches': mismatches,
                         'imports': imports, 'sourceSha256': file_sha256(directory / FIXTURE.name)}
    for root in SIGNATURES:
        if results['original']['imports'][root]['status'] != results['renamed']['imports'][root]['status']:
            raise HarnessError('helper renaming changed storage-reference admission')
    manifest = {
        'scope': 'source-only storage regression preparation; importer observations, no admission fix',
        'verityHead': command(['git', 'rev-parse', 'HEAD'], cwd=ROOT).strip(),
        'worktreeStatus': command(['git', 'status', '--porcelain'], cwd=ROOT),
        'compiler': compiler, 'settings': SETTINGS,
        'anvilSha256': file_sha256(Path(shutil.which('anvil'))),
        'files': {str(p.relative_to(ROOT)): file_sha256(p) for p in (
            FIXTURE, Path(__file__), Path(__file__).with_name('storage_reference_oracle.py'),
            Path(__file__).with_name('anvil.py'), ROOT / 'scripts/keccak256.py')},
        'expectationsSha256': {str(i): file_sha256(output / f'expectations-layout-{i}.json')
                               for i in specs},
        'packedExpectationsSha256': file_sha256(output / 'packed-expectations.json'),
        'initialState': 'explicit physical storage installed identically before each discovery/replay',
        'missingRoutes': ['model', 'compiled'], 'threeRouteAgreement': False,
        'proofStatus': 'finite source execution only; no new theorem or correspondence claim',
        'limits': ['pinned downstream helper/wrapper validation remains pending',
                   'no gas/resource, constructor, or complete application equivalence'],
    }
    write_json(output / 'manifest.json', manifest)
    write_json(output / 'results.json', {'sourcePreparationPassed': True,
        'threeRouteAgreement': False, 'variants': results})
    print(f'{len(specs[0]["transactions"])} transactions per replay; '
          f'{len(POSITIVE)} positive variants; {len(MUTANTS)} source mutants detected; '
          'model/compiled sequence validation pending')
    # Source-only evidence cannot satisfy the milestone gate, even if every root later admits.
    return 1 if require_three_routes else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    parser.add_argument('--require-three-routes', action='store_true')
    args = parser.parse_args()
    try:
        return run(args.output, prepared=args.prepared, require_three_routes=args.require_three_routes)
    except (HarnessError, OSError) as exc:
        print(json.dumps({'infrastructureFailure': str(exc)}))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
