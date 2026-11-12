"""Three-route Cancun hash harness; blocked imports never count as semantic agreement."""
import argparse
from pathlib import Path
import sys
from subprocess import SubprocessError

from keccak256 import keccak_256, selector
from setup_solc_import import file_sha256
from .check_packed_memory_hash import (
    CONCRETE_HASH, CONCRETE_PREIMAGE, FIXTURE, SETTINGS, SHIFTS,
    packed_preimage, variants, vectors, word,
)
from .check_packed_memory_hash_import import ROOTS, check_controls
from .engine import HarnessError, ROOT, command, implementation_hashes, write_json
from .hash_execution import (
    TIMESTAMP, YUL_SETTINGS, compare_expectations, compare_routes, compile_generated,
    compile_source, execute_evm, import_root, pinned_compiler, snapshot_root,
    validate_cases, verify_abi,
)

CONTROL = '''// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;
contract WordHash {
    function digest(bytes32 tag) public pure returns (bytes32) {
        return keccak256(abi.encode(tag));
    }
}
'''
ZERO_WORD_HASH = '290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563'


def expectations():
    rows = [{'values': list(map(str, values)), 'preimage': packed_preimage(*values).hex(),
             'hash': keccak_256(packed_preimage(*values)).hex()} for values in vectors()]
    if (rows[0]['preimage'], rows[0]['hash']) != (CONCRETE_PREIMAGE, CONCRETE_HASH):
        raise HarnessError('fixed packed expectation changed')
    return rows


def case(ident, signature, args, expected):
    return {'id': ident, 'args': [str(n % 2**256) for n in args],
            'calldata': selector(signature) + b''.join(map(word, args)).hex(),
            'expected': '0x' + expected, 'storage': [], 'observe': [],
            'timestamp': str(TIMESTAMP)}


def packed_cases(root, expected):
    rows = []
    for index, row in enumerate(expected):
        args = tuple(map(int, row['values']))
        for shift in ((None,) if root == 'digest' else SHIFTS):
            inputs = args if shift is None else (*args, shift)
            suffix = '' if shift is None else b''.join(map(word, (0, 0, 0, 0, 0xfeed))).hex()
            rows.append(case(f'{index}:{shift}', ROOTS[root], inputs, row['hash'] + suffix))
    return rows


def control_cases():
    values = list(dict.fromkeys([0, 1, 2**255, 2**256 - 1,
                                int.from_bytes(bytes(range(32)), 'big')]
                               + [row[3] for row in vectors()]))
    rows = [case(str(index), 'digest(bytes32)', [value], keccak_256(word(value)).hex())
            for index, value in enumerate(values)]
    if rows[0]['expected'] != '0x' + ZERO_WORD_HASH:
        raise HarnessError('fixed word-hash control expectation changed')
    return rows


def run_root(directory, filename, contract, signature, cases, built, solc, compiler, mutant):
    directory.mkdir()
    validate_cases(signature, cases)
    verify_abi(built, signature, cases)
    write_json(directory / 'cases.json', cases)
    source, context = execute_evm(directory / 'source-evm', built, cases)
    outcome = {'source': compare_expectations(source, cases, mutant)}
    admission = import_root(directory, filename, contract, signature)
    if admission['status'] == 'rejected':
        return {**admission, 'execution': {'status': 'blocked', 'source': outcome['source'],
                'denote': 'blocked by located importer rejection',
                'generatedEvm': 'blocked by located importer rejection',
                'semanticAgreement': 'not tested'}}
    snapshot = snapshot_root(directory, filename, contract, signature, cases, context, compiler)
    outcome['denote'] = compare_expectations(snapshot['results'], cases, mutant)
    generated = compile_generated(directory, snapshot, solc)
    compiled, _ = execute_evm(directory / 'generated-evm', generated, cases, context)
    outcome['generatedEvm'] = compare_expectations(compiled, cases, mutant)
    compare_routes({'source': source, 'denote': snapshot['results'], 'compiled': compiled}, cases)
    return {**admission, 'model': snapshot['model'], 'sourceDigest': snapshot['digest'],
            'execution': {'status': 'executed', 'routes': outcome,
                          'semanticAgreement': 'finite three-route agreement',
                          'compilerProof': snapshot['compilerProof']}}


def run(output, *, prepared=False, require_admission=False):
    output = output.resolve()
    if not output.is_relative_to(ROOT):
        raise HarnessError('output must be inside this checkout for importer package discovery')
    output.mkdir(parents=True, exist_ok=False)
    solc, compiler = pinned_compiler()
    expected = expectations()
    write_json(output / 'expectations.json', expected)
    implementation = implementation_hashes()
    revision = command(['git', 'rev-parse', 'HEAD'], cwd=ROOT).strip()
    manifest = {
        'scope': 'stateless hash returns: source EVM / actual imported Denote / generated EVM',
        'verityHead': revision,
        'worktreeStatus': command(['git', 'status', '--porcelain'], cwd=ROOT),
        'sourceCompiler': compiler, 'generatedCompiler': compiler,
        'sourceSettings': SETTINGS, 'generatedSettings': YUL_SETTINGS,
        'generatedSettingsNote': 'Yul input uses the optimizer directly; Solidity viaIR and '
                                 'metadata settings do not apply to Yul.',
        'executionFork': 'cancun', 'expectationsSha256': file_sha256(output / 'expectations.json'),
        'fixtureSha256': file_sha256(FIXTURE), 'implementationFiles': implementation,
        'independentOracleSha256': file_sha256(ROOT / 'scripts/keccak256.py'),
        'inputCases': len(expected), 'shifts': SHIFTS,
        'proofStatus': 'finite executable evidence; no source/importer or cryptographic proof',
        'limits': ['pure roots with static ABI and empty initial storage only',
                   'no storage-frame, gas/OOG, arbitrary-memory or whole-contract claim',
                   'no supported route substituted for a rejected packed root'],
    }
    write_json(output / 'manifest.json', manifest)
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.Differential', '--project-dir', ROOT],
                cwd=ROOT, timeout=1800, log=output / 'build.log')
    rows = {}
    sources = {'control': CONTROL, **variants(FIXTURE.read_text())}
    for name, source in sources.items():
        directory = output / name
        directory.mkdir()
        filename, contract = ('WordHash.sol', 'WordHash') if name == 'control' else (
            FIXTURE.name, 'PackedMemoryHash')
        (directory / filename).write_text(source)
        built = compile_source(directory, filename, contract, solc)
        signatures = {'digest': 'digest(bytes32)'} if name == 'control' else ROOTS
        rows[name] = {}
        for root, signature in signatures.items():
            cases = control_cases() if name == 'control' else packed_cases(root, expected)
            rows[name][root] = run_root(directory / root, filename, contract, signature,
                                       cases, built, solc, compiler,
                                       name in ('padded', 'changed-body'))
        if name == 'control' and rows[name]['digest']['status'] != 'admitted':
            raise HarnessError('required three-route hash control was rejected')
    if (command(['git', 'rev-parse', 'HEAD'], cwd=ROOT).strip() != revision
            or implementation_hashes() != implementation
            or file_sha256(FIXTURE) != manifest['fixtureSha256']
            or file_sha256(solc) != compiler['sha256']):
        raise HarnessError('source, implementation, revision or compiler changed during campaign')
    admitted = check_controls(rows)
    results = {
        'observationsComplete': True, 'controlsPassed': True,
        'requiredRootsAdmitted': admitted,
        'packedSemanticAgreement': 'finite three-route agreement' if admitted else 'blocked',
        'routes': {name: {root: {k: v for k, v in row.items() if k != 'model'}
                          for root, row in roots.items()} for name, roots in rows.items()},
    }
    write_json(output / 'results.json', results)
    print(f"Hash control passes all three routes; {len(expected)} packed inputs; "
          f"packed semantic agreement: {results['packedSemanticAgreement']}")
    return 1 if require_admission and not admitted else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true', help='reuse built importer and runner')
    parser.add_argument('--require-admission', action='store_true',
                        help='fail until original and renamed digest/inspect execute all routes')
    args = parser.parse_args()
    try:
        return run(args.output, prepared=args.prepared, require_admission=args.require_admission)
    except (HarnessError, OSError, ValueError, KeyError, TypeError, IndexError, SubprocessError) as error:
        print(f'harness failure: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
