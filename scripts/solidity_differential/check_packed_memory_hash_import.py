"""Observe packed-memory importer boundaries; optionally require root admission.

This is preparation for the importer fix, not a semantic correspondence check.
The source campaign's byte/hash oracle and source mutations are reused unchanged.
"""
import argparse
import json
from pathlib import Path
import re

from keccak256 import keccak_256
from setup_solc_import import RELEASES, file_sha256, host_platform
from .check_packed_memory_hash import (
    CONCRETE_HASH, CONCRETE_PREIMAGE, FIXTURE, SETTINGS, packed_preimage, variants, vectors,
)
from .engine import HarnessError, ROOT, command, run_bounded, solc_compile, write_json

ROOTS = {
    'digest': 'digest(address,int24,int24,bytes32)',
    'inspect': 'inspect(address,int24,int24,bytes32,uint256)',
}
CONTROL = '''pragma solidity 0.8.26;
contract ScalarIdentity {
    function echo(uint256 word) public pure returns(uint256) { return word; }
}
'''
MARKER = 'PACKED_IMPORT_ARTIFACT:'


def driver_text(directory, filename, contract, signature, *, describe=False):
    text = ('import Compiler.SolidityImport.Import\n'
            'open Compiler.CompilationModel.SolidityImport\n'
            f'solidity_import imported from {json.dumps(str(directory))} '
            f'entry {json.dumps(filename)}\n'
            '  using { solc := "0.8.26+commit.8a97fa7a", evmVersion := "cancun", '
            'viaIR := true, optimizerRuns := some 44444444, bytecodeHash := "none" }\n'
            f'  contract {contract}\n  function {signature}\n')
    if describe:
        # Emit artifacts on stdout: eval cache hits must not skip filesystem writes.
        text += ('#eval IO.println ("' + MARKER + '" ++ Lean.Json.compress (Lean.Json.mkObj [\n'
                 '  ("model", Lean.toJson (toString (repr imported.model))),\n'
                 '  ("report", Lean.toJson imported.report.toText),\n'
                 '  ("sourceDigest", Lean.toJson imported.sourceDigest)]))\n')
    return text


def classify(returncode, reply, source, filename, contract, root):
    """A tool failure can never satisfy an unsupported-source observation."""
    if (returncode not in (0, 1) or reply.get('crashed') is not False
            or reply.get('timed_out') is not False or reply.get('import_ok') is not True
            or type(reply.get('ok')) is not bool):
        raise HarnessError('import evaluation infrastructure failed')
    errors = reply.get('errors')
    if not isinstance(errors, list) or any(not isinstance(s, str) for s in errors):
        raise HarnessError('malformed importer diagnostics')
    if reply['ok'] and returncode == 0 and not errors:
        return {'status': 'admitted'}
    if reply['ok'] or returncode == 0:
        raise HarnessError('inconsistent importer exit status')
    if len(errors) != 1:
        raise HarnessError('expected one source rejection, without additional evaluation errors')
    diagnostic = errors[0]
    pattern = (re.escape(filename) + r':([1-9][0-9]*):([1-9][0-9]*): (\w+): '
               r'\[solidity-import:unsupported\] ([^\n]+)\nclosure: ([^\n]+)')
    matches = list(re.finditer(pattern, diagnostic))
    if len(matches) != 1 or diagnostic.count('[solidity-import:unsupported]') != 1:
        raise HarnessError('missing unambiguous located importer rejection')
    match = matches[0]
    line, column = map(int, match.group(1, 2))
    lines = source.splitlines()
    if (line > len(lines) or column > len(lines[line - 1].encode())
            or f'{contract}.{root}' not in match.group(5).split(' -> ')):
        raise HarnessError('importer rejection has an invalid source location or closure')
    return {'status': 'rejected', 'line': line, 'column': column,
            'node': match.group(3), 'reason': match.group(4), 'closure': match.group(5)}


def evaluate(driver):
    result = run_bounded(['turbo-lean', '--json', 'eval', driver, '--project-dir', ROOT,
                          '--timeout-ms', '180000'], cwd=ROOT, timeout=210)
    driver.with_suffix('.stdout.json').write_text(result.stdout)
    driver.with_suffix('.stderr.log').write_text(result.stderr)
    try:
        reply = json.loads(result.stdout)
    except ValueError as error:
        raise HarnessError('Turbo-Lean did not return a JSON evaluation result') from error
    if not isinstance(reply, dict):
        raise HarnessError('malformed Turbo-Lean evaluation result')
    return result.returncode, reply


def observe(directory, filename, contract, signature):
    root = signature.split('(')[0]
    source = (directory / filename).read_text()
    driver = directory / f'{root}.lean'
    driver.write_text(driver_text(directory, filename, contract, signature))
    code, reply = evaluate(driver)
    observation = classify(code, reply, source, filename, contract, root)
    if observation['status'] == 'admitted':
        driver = directory / f'{root}-artifact.lean'
        driver.write_text(driver_text(directory, filename, contract, signature, describe=True))
        code, reply = evaluate(driver)
        if classify(code, reply, source, filename, contract, root)['status'] != 'admitted':
            raise HarnessError('accepted import failed to produce its model/report')
        lines = (reply.get('stdout', '') + '\n' + '\n'.join(reply.get('messages', []))).splitlines()
        artifacts = [line[len(MARKER):] for line in lines if line.startswith(MARKER)]
        if len(artifacts) != 1:
            raise HarnessError('missing unambiguous model/report artifact')
        artifact = json.loads(artifacts[0])
        if any(not isinstance(artifact.get(k), str) or not artifact[k]
               for k in ('model', 'report', 'sourceDigest')):
            raise HarnessError('incomplete model/report artifact')
        write_json(directory / f'{root}-artifact.json', artifact)
        observation['model'] = artifact['model']
        observation['sourceDigest'] = artifact['sourceDigest']
    return observation


def check_controls(rows):
    for root in ROOTS:
        original, renamed = rows['original'][root], rows['renamed'][root]
        if original['status'] != renamed['status']:
            raise HarnessError(f'{root}: helper renaming changed importer support')
        if original['status'] == 'rejected':
            for key in ('node', 'reason', 'closure'):
                if original[key] != renamed[key].replace('renamedPacked', 'hashPacked'):
                    raise HarnessError(f'{root}: helper renaming changed the rejection boundary')
        else:
            for name in ('padded', 'changed-body'):
                mutant = rows[name][root]
                if mutant['status'] == 'admitted' and mutant['model'] == original['model']:
                    raise HarnessError(f'{root}: {name} body change left the imported model unchanged')
    return all(rows[name][root]['status'] == 'admitted'
               for name in ('original', 'renamed') for root in ROOTS)


def helper_controls(source, extra_names=()):
    """Vary helper spelling and unreachable storage without changing its body."""
    names = tuple(dict.fromkeys(('hashPacked', 'renamedPacked', *extra_names)))
    if any(not re.fullmatch(r'[A-Za-z_$][A-Za-z0-9_$]*', name) for name in names):
        raise HarnessError('helper names must be Solidity identifiers')
    anchor = 'contract PackedMemoryHash {'
    if source.count(anchor) != 1:
        raise HarnessError('storage declaration control anchor changed')
    sources = variants(source)
    for name_index, name in enumerate(names):
        for count in (0, 1, 2):
            fields = ''.join(f' uint256 private unusedStorage{i};' for i in range(count))
            for body in ('original', 'padded', 'changed-body'):
                control = sources[body].replace('hashPacked', name).replace(anchor, anchor + fields)
                yield f'helper-{name_index}-storage-{count}-{body}', {
                    'helper': name, 'storageDeclarations': count, 'body': body, 'source': control,
                }


def check_helper_controls(rows, controls):
    """Names and unused storage must never turn an unsupported body into a model."""
    for label, control in controls.items():
        expected = rows[control['body']]['digest']
        actual = control['observation']
        if expected['status'] != actual['status']:
            raise HarnessError(f'{label}: helper name or unused storage changed importer support')
        if expected['status'] == 'rejected':
            for key in ('node', 'reason', 'closure'):
                normalized = actual[key].replace('PackedMemoryHash.' + control['helper'],
                                                 'PackedMemoryHash.hashPacked')
                if expected[key] != normalized:
                    raise HarnessError(f'{label}: helper name or unused storage changed rejection')


def run(output, *, prepared=False, require_admission=False, helper_names=()):
    output = output.resolve()
    if not output.is_relative_to(ROOT):
        raise HarnessError('output must be inside this checkout for importer package discovery')
    output.mkdir(parents=True, exist_ok=False)
    solc = ROOT / '.lake/solidity-import/solc-0.8.26'
    if not solc.is_file() or file_sha256(solc) != RELEASES['0.8.26']['sha256'][host_platform()]:
        raise HarnessError('missing or changed pinned Solidity 0.8.26 compiler')
    if not prepared:
        command(['turbo-lean', 'build', 'Compiler.SolidityImport.Import', '--project-dir', ROOT],
                cwd=ROOT, timeout=1800, log=output / 'build.log')
    expected = [{'values': list(map(str, values)), 'preimage': packed_preimage(*values).hex(),
                 'hash': keccak_256(packed_preimage(*values)).hex()} for values in vectors()]
    if (expected[0]['preimage'], expected[0]['hash']) != (CONCRETE_PREIMAGE, CONCRETE_HASH):
        raise HarnessError('fixed concrete expectation changed')
    write_json(output / 'expectations.json', expected)
    metadata = {
        'scope': 'importer admission and source-body sensitivity only',
        'extraHelperNames': list(helper_names),
        'verityHead': command(['git', 'rev-parse', 'HEAD'], cwd=ROOT).strip(),
        'worktreeStatus': command(['git', 'status', '--porcelain'], cwd=ROOT),
        'sourceCompilerSha256': file_sha256(solc), 'settings': SETTINGS,
        'expectationsSha256': file_sha256(output / 'expectations.json'),
        'files': {str(path.relative_to(ROOT)): file_sha256(path) for path in
                  (FIXTURE, Path(__file__), ROOT / 'scripts/solidity_differential/check_packed_memory_hash.py')},
        'importedSemantics': 'not run', 'generatedOutput': 'not run',
        'proofStatus': 'no correspondence proof; admission is not semantic correctness',
    }
    write_json(output / 'manifest.json', metadata)
    rows = {}
    for name, source in {'control': CONTROL, **variants(FIXTURE.read_text())}.items():
        directory = output / name
        directory.mkdir()
        filename = 'ScalarIdentity.sol' if name == 'control' else FIXTURE.name
        contract = 'ScalarIdentity' if name == 'control' else 'PackedMemoryHash'
        (directory / filename).write_text(source)
        # Establish source validity independently before interpreting importer errors.
        solc_compile({'language': 'Solidity', 'sources': {filename: {'content': source}},
                      'settings': {**SETTINGS, 'outputSelection': {'*': {'': ['ast'],
                                   '*': ['abi', 'storageLayout']}}}},
                     directory, directory / 'solc', solc=solc)
        signatures = {'echo': 'echo(uint256)'} if name == 'control' else ROOTS
        rows[name] = {root: observe(directory, filename, contract, signature)
                      for root, signature in signatures.items()}
        if name == 'control' and rows[name]['echo']['status'] != 'admitted':
            raise HarnessError('required scalar import control failed')
    admitted = check_controls(rows)
    controls = {}
    for label, control in helper_controls(FIXTURE.read_text(), helper_names):
        directory = output / label
        directory.mkdir()
        source = control.pop('source')
        (directory / FIXTURE.name).write_text(source)
        solc_compile({'language': 'Solidity', 'sources': {FIXTURE.name: {'content': source}},
                      'settings': {**SETTINGS, 'outputSelection': {'*': {'': ['ast'],
                                   '*': ['abi', 'storageLayout']}}}},
                     directory, directory / 'solc', solc=solc)
        control['observation'] = observe(directory, FIXTURE.name, 'PackedMemoryHash', ROOTS['digest'])
        controls[label] = control
    # Retain all observations even when a regression in this matrix is detected.
    write_json(output / 'helper-controls.json', controls)
    check_helper_controls(rows, controls)
    write_json(output / 'results.json', {
        'observationsComplete': True, 'controlsPassed': True,
        'requiredRootsAdmitted': admitted, 'semanticAgreement': 'not tested',
        'routes': {name: {root: {k: v for k, v in row.items() if k != 'model'}
                          for root, row in roots.items()} for name, roots in rows.items()},
    })
    count = sum(row['status'] == 'rejected' for name in variants(FIXTURE.read_text())
                for row in rows[name].values())
    print(f'8 importer observations; {count} located rejections; '
          f'{len(controls)} helper/storage controls passed; '
          f'required roots admitted: {admitted}; semantics not tested')
    return 1 if require_admission and not admitted else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true', help='reuse an already built importer')
    parser.add_argument('--require-admission', action='store_true',
                        help='fail until original and renamed digest/inspect roots are admitted')
    parser.add_argument('--helper-name', action='append', default=[],
                        help='additional helper spelling to test with zero, one and two unused fields')
    args = parser.parse_args()
    return run(args.output, prepared=args.prepared, require_admission=args.require_admission,
               helper_names=args.helper_name)


if __name__ == '__main__':
    raise SystemExit(main())
