"""Prepare full-cleanup rollback regressions without changing importer admission."""
import argparse
import json
from pathlib import Path

from keccak256 import selector
from setup_solc_import import file_sha256
from .check_packed_memory_hash_import import driver_text, observe
from .check_packed_storage_read import require_rejection
from .check_packed_storage_updates import EFFECT_REJECTION
from .check_storage_reference import CONTRACT, FIXTURE, compile_variant, source_adapter, variants
from .check_storage_reference_routes import (
    CONTRACT as CONTROL_CONTRACT, FIXTURE as CONTROL_FIXTURE, SIGNATURES as CONTROL_SIGNATURES,
    STATE_ARCHIVES, build_source, control_inputs, require_outcome, run_routes,
)
from .engine import HarnessError, ROOT, command, write_json
from .hash_execution import compile_generated, pinned_compiler
from .identity import ImplementationIdentity
from .pinned_sequence import SENDERS, create_address
from .storage_reference_oracle import PACKED_ARCHIVE_SHA256, SIGNATURES, replay_expected, specification
from .stateful import ROUTES
from .storage_sequence_execution import eval_json, prepare_model

POSITIVE = ('original', 'renamed', 'shifted-layout', 'void-return')
MUTANTS = ('drop-revert', 'wrong-error-argument', 'wrong-error-selector', 'empty-revert')
COMPILER_REJECTION = (
    "Compilation error: function 'writeThenRevert' declares return values but not all "
    'control-flow paths end in return/revert (Issue #738 (exhaustive return-path analysis))')
COMPILATION_MARKER = 'ROLLBACK_COMPILATION:'
TAIL_CASES = {
    'zero': ('[guard]', True),
    'nonzero': ('[.requireError (.literal 1) name args]', False),
    'unknown': ('[.requireError (.param "next") name args]', False),
    'stop': ('[.stop]', False),
    'conditional-fallthrough': ('[.ite (.param "next") [guard] []]', False),
    'both-branches-revert': ('[.ite (.param "next") [guard] [.revertEmpty]]', True),
    'unreachable-stop': ('[guard, .stop]', True),
}


def replace_once(source, before, after):
    if source.count(before) != 1:
        raise HarnessError('rollback source anchor changed')
    return source.replace(before, after, 1)


def source_variants(source):
    """Only mutate source copies; retain the original fixture and all expected observations."""
    full = variants(source)['full-cleanup']
    choices = variants(full)
    returns = ('function writeThenRevert(address account, int24 left, int24 right, '
               'bytes32 salt, uint128 next)\n        external')
    result = {name: choices[name] for name in ('original', 'renamed', 'shifted-layout',
                                              'drop-revert')}
    result['void-return'] = replace_once(full, returns + ' returns (uint128, uint256, uint256)',
                                        returns)
    result['wrong-error-argument'] = replace_once(full, 'revert Rejected(next);',
                                                 'revert Rejected(next ^ 1);')
    result['wrong-error-selector'] = full.replace('Rejected(', 'DifferentRejected(')
    result['empty-revert'] = replace_once(full, 'revert Rejected(next);', 'revert();')
    return result


def require_source_result(result, spec, mutant=None):
    """Require executed semantic differences, including the subsequent reads after rollback."""
    if (result.get('routes') != ['source']
            or set(result.get('mismatches', {})) != {'source'}):
        raise HarnessError('rollback preparation requires the actual source route')
    rows = result['mismatches']['source']
    ids = {tx['id'] for tx in spec['transactions']}
    if (len({row['id'] for row in rows}) != len(rows)
            or any(row['id'] not in ids or not row['fields'] for row in rows)):
        raise HarnessError('invalid rollback mutation observations')
    failures = {row['id']: set(row['fields']) for row in rows}
    reverted = {row['id'] for row in spec['expected'] if row['status'] == 'revert'}
    if mutant is None:
        if rows:
            raise HarnessError('independent full-cleanup rollback expectations differ')
    elif mutant == 'drop-revert':
        if (any(failures.get(ident) != {'status', 'data', 'events', 'storage'}
                for ident in reverted)
                or any(fields - {'data', 'storage'} for ident, fields in failures.items()
                       if ident not in reverted)
                or not any(tx['function'] == 'read'
                           and failures.get(tx['id']) == {'data', 'storage'}
                           for tx in spec['transactions'])):
            raise HarnessError('removed revert must expose writes, logs and later read corruption')
    elif mutant in MUTANTS:
        if failures != {ident: {'data'} for ident in reverted}:
            raise HarnessError('error-payload mutant must change only every exact revert payload')
    else:
        raise HarnessError('unknown rollback mutation')


def require_compilation(result, terminal=True):
    expected = ({'status': 'compiled'} if terminal
                else {'status': 'rejected', 'reason': COMPILER_REJECTION})
    if result != expected:
        raise HarnessError('terminal custom-error compilation boundary changed')


def probe_compilation(directory, source, contract, signature, tail_case='zero'):
    """Distinguish a structured compiler rejection from importer or tool failure."""
    if tail_case not in TAIL_CASES:
        raise HarnessError('unknown control-flow boundary case')
    tail, _ = TAIL_CASES[tail_case]
    driver = directory / f'Compilation-{tail_case}.lean'
    header = 'import Compiler.Codegen\n' + driver_text(source.parent, source.name,
                                                     contract, signature)
    driver.write_text(header + f'''\n#eval do
  let [fn] := imported.model.functions | throw (IO.userError "expected one control root")
  let some guard@(.requireError (.literal 0) name args) := fn.body.getLast?
    | throw (IO.userError "expected imported literal-zero custom-error guard")
  let tail : List Compiler.CompilationModel.Stmt := {tail}
  let active := {{ imported.model with functions := [{{ fn with body := fn.body.dropLast ++ tail }}] }}
  let result := Compiler.CompilationModel.compile active [{int(selector(signature), 16)}] .cancun
  let observation := match result with
    | .ok _ => Lean.Json.mkObj [("status", Lean.toJson ("compiled" : String))]
    | .error reason => Lean.Json.mkObj [("status", Lean.toJson ("rejected" : String)),
        ("reason", Lean.toJson reason)]
  IO.println ({json.dumps(COMPILATION_MARKER)} ++ observation.compress)
''')
    return eval_json(driver, COMPILATION_MARKER)


def require_error_mutation(result, spec):
    """All actual routes must preserve rollback while detecting exactly the changed payloads."""
    expected = [{'id': row['id'], 'fields': ['data']}
                for row in spec['expected'] if row['status'] == 'revert']
    if (result.get('routes') != list(ROUTES) or result.get('divergences') != []
            or result.get('mismatches') != {route: expected for route in ROUTES}):
        raise HarnessError('custom-error mutation requires exact three-route payload evidence')


def execute_declared_control(directory, source, built, spec, solc, compiler):
    """The original declared-return control now must execute, including exact rollback bytes."""
    driver, snapshot = prepare_model(directory / 'model', source, CONTROL_CONTRACT,
                                     list(CONTROL_SIGNATURES.values()), compiler)
    compiled = compile_generated(directory / 'model', snapshot, solc)
    result = run_routes(directory / 'routes', spec, source, built, driver, compiled)
    require_outcome(result)
    mutated_source = replace_once(source.read_text(), 'revert Rejected(next);',
                                   'uint128 changedError = next ^ 1; revert Rejected(changedError);')
    mutated = directory / 'wrong-error-argument'
    bad_source, bad_built = build_source(mutated, mutated_source, solc)
    bad_driver, bad_snapshot = prepare_model(mutated / 'model', bad_source, CONTROL_CONTRACT,
                                             list(CONTROL_SIGNATURES.values()), compiler)
    bad_compiled = compile_generated(mutated / 'model', bad_snapshot, solc)
    bad = run_routes(mutated / 'routes', spec, bad_source, bad_built, bad_driver, bad_compiled)
    require_error_mutation(bad, spec)
    return {'threeRouteAgreement': True, 'errorPayloadMutationDetected': True}


def run(output, *, prepared=False, require_composition=False):
    output = output.resolve()
    if not output.is_relative_to(ROOT):
        raise HarnessError('output must be inside the checkout')
    output.mkdir(parents=True, exist_ok=False)
    solc, compiler = pinned_compiler()
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.SequenceRunner', 'Compiler.SolidityImport.Differential',
                 '--project-dir', ROOT], cwd=ROOT, timeout=1800,
                log=output / 'build.log')
    identity = ImplementationIdentity(FIXTURE, extra_inputs=(CONTROL_FIXTURE,))
    specs = {shift: specification(create_address(SENDERS[0]), SENDERS[0], shift)
             for shift in (0, 1)}
    for shift, spec in specs.items():
        path = output / f'expectations-layout-{shift}.json'
        write_json(path, spec)
        if file_sha256(path) != STATE_ARCHIVES[shift]:
            raise HarnessError('independent full state expectations changed')
    path = output / 'packed-expectations.json'
    write_json(path, specs[0]['packedExpectations'])
    if file_sha256(path) != PACKED_ARCHIVE_SHA256:
        raise HarnessError('independent packed expectations changed')
    results = {}
    for name, source in source_variants(FIXTURE.read_text()).items():
        directory = output / name
        directory.mkdir()
        built = compile_variant(directory, source, solc)
        spec = specs[int(name == 'shifted-layout')]
        result = replay_expected(spec,
            {'source': source_adapter(directory / 'execution', built, spec)},
            required_routes=('source',))
        write_json(directory / 'execution.json', result)
        require_source_result(result, spec, name if name in MUTANTS else None)
        results[name] = {'sourceExpectationsPassed': name in POSITIVE,
                         'sourceMutationDetected': name in MUTANTS,
                         'mismatches': result['mismatches']}
        if name in POSITIVE:
            admission = observe(directory, FIXTURE.name, CONTRACT, SIGNATURES['writeThenRevert'])
            require_rejection(admission, EFFECT_REJECTION)
            results[name]['admission'] = admission
    # Supplied-key controls do not substitute for packed-hash composition evidence.
    controls = {}
    for declared in (False, True):
        name = 'declared-return-control' if declared else 'void-control'
        source = CONTROL_FIXTURE.read_text()
        if declared:
            anchor = 'function writeThenRevert(bytes32 key, uint128 next)\n        external'
            source = replace_once(source, anchor,
                                  anchor + ' returns (uint128, uint256, uint256)')
        directory = output / name
        path, built = build_source(directory, source, solc)
        spec = control_inputs(specs[0])
        result = replay_expected(spec,
            {'source': source_adapter(directory / 'execution', built, spec)},
            required_routes=('source',))
        write_json(directory / 'execution.json', result)
        require_source_result(result, spec)
        signature = CONTROL_SIGNATURES['writeThenRevert']
        admission = observe(directory, path.name, CONTROL_CONTRACT, signature)
        if admission['status'] != 'admitted':
            raise HarnessError('supplied-key rollback control must remain importable')
        compilation = probe_compilation(directory, path, CONTROL_CONTRACT, signature)
        require_compilation(compilation)
        controls[name] = {'sourceExpectationsPassed': True, 'admission': admission,
                          'compilation': compilation}
        if declared:
            boundaries = {'zero': compilation}
            for case, (_, terminal) in TAIL_CASES.items():
                if case == 'zero':
                    continue
                observation = probe_compilation(directory, path, CONTROL_CONTRACT, signature, case)
                require_compilation(observation, terminal)
                boundaries[case] = observation
            controls[name]['boundaries'] = boundaries
            controls[name]['execution'] = execute_declared_control(
                directory, path, built, spec, solc, compiler)
    identity.verify()
    write_json(output / 'implementation.json', identity.manifest)
    write_json(output / 'results.json', {'rollbackPreparationPassed': True,
        'packedRollbackThreeRouteAgreement': False, 'variants': results, 'controls': controls,
        'missingPackedRoutes': ['model', 'compiled']})
    write_json(output / 'manifest.json', {'verityHead': identity.manifest['revision'],
        'compiler': compiler, 'fork': 'cancun', 'stateArchivesSha256': STATE_ARCHIVES,
        'packedArchiveSha256': PACKED_ARCHIVE_SHA256,
        'scope': 'complete frozen sequence; packed source EVM and supplied-key three-route rollback',
        'limits': ['no packed rollback admission change',
                   'packed Denote/generated-EVM composition remains blocked',
                   'no tail-only cleanup, downstream wrapper or gas/resource equivalence']})
    print('Full-cleanup source rollback and exact errors pass; mutation sensitivity verified; '
          'packed Denote/generated-EVM rollback remains blocked')
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
