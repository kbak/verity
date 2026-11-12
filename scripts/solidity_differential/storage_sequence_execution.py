"""Actual imported-model snapshots and warm Denote sequence execution for storage controls."""
import json
from pathlib import Path
import re
import sys

from keccak256 import selector
from .check_packed_memory_hash import SETTINGS
from .check_packed_memory_hash_import import driver_text, evaluate
from .engine import HarnessError, write_json

SNAPSHOT_MARKER = 'STORAGE_MODEL_SNAPSHOT:'
SEQUENCE_MARKER = 'STORAGE_DENOTE_SEQUENCE:'


def eval_json(driver, marker):
    """Read one actual evaluation result; cached stdout must contain the entire artifact."""
    code, reply = evaluate(driver)
    if (code != 0 or reply.get('ok') is not True or reply.get('import_ok') is not True
            or reply.get('crashed') is not False or reply.get('timed_out') is not False
            or reply.get('errors') != []):
        raise HarnessError(f'actual storage model evaluation failed: {driver}')
    lines = (reply.get('stdout', '') + '\n' + '\n'.join(reply.get('messages', []))).splitlines()
    artifacts = [line[len(marker):] for line in lines if line.startswith(marker)]
    if len(artifacts) != 1:
        raise HarnessError('missing or duplicate storage model artifact')
    try:
        return json.loads(artifacts[0])
    except ValueError as exc:
        raise HarnessError('malformed storage model artifact') from exc


def validate_snapshot(snapshot, signatures, contract, compiler, mutation):
    """Require the actual source profile, complete root inventory and explicit compiler target."""
    names = [s.split('(')[0] for s in signatures]
    counts = [len(s.split('(')[1][:-1].split(',')) for s in signatures]
    if (not isinstance(snapshot, dict) or snapshot.get('roots') != names
            or snapshot.get('signatures') != list(signatures) or snapshot.get('paramCounts') != counts
            or snapshot.get('selectors') != [int(selector(s), 16) for s in signatures]
            or snapshot.get('contract') != contract or snapshot.get('targetFork') != 'cancun'
            or snapshot.get('denoteCovered') is not True or snapshot.get('mutation') != mutation
            or snapshot.get('solcLongVersion') != compiler['longVersion']
            or snapshot.get('solcSha256') != compiler['sha256']):
        raise HarnessError('storage model profile, roots or selectors changed')
    for key in ('model', 'importedModel', 'report', 'digest', 'settings', 'yul'):
        if not isinstance(snapshot.get(key), str) or not snapshot[key]:
            raise HarnessError('incomplete storage model provenance')
    if not re.fullmatch(r'[0-9a-f]{64}', snapshot['digest']):
        raise HarnessError('invalid storage model source digest')
    if (snapshot['model'] == snapshot['importedModel']) != (mutation == 'none'):
        raise HarnessError('model mutation was omitted or applied to the baseline')
    proofs = snapshot.get('compilerProof')
    if not isinstance(proofs, list) or len(proofs) != len(names) or any(
            not isinstance(p, str) or not p for p in proofs):
        raise HarnessError('missing per-root compiler proof status')
    settings = json.loads(snapshot['settings'])
    if (not isinstance(settings, dict)
            or any(settings.get(k) != v for k, v in SETTINGS.items())
            or set(settings) - set(SETTINGS) - {'outputSelection', 'remappings'}
            or settings.get('remappings', []) != []):
        raise HarnessError('imported storage compiler settings changed')


def prepare_model(directory, source, contract, signatures, compiler, mutation='none'):
    """Import all real roots, optionally mutate event statements, and compile that model to Yul."""
    if mutation not in ('none', 'drop-events'):
        raise HarnessError('unknown storage model mutation')
    directory.mkdir(parents=True, exist_ok=False)
    roots = '\n'.join('  function ' + s for s in signatures) + '\n'
    header = driver_text(source.parent, source.name, contract, signatures[0])
    header = header.replace('  function ' + signatures[0] + '\n', roots)
    header = ('import Compiler.SolidityImport.SequenceRunner\n'
              'import Compiler.SolidityImport.Differential\n'
              'import Compiler.Codegen\nimport Compiler.Yul.PrettyPrint\n'
              + header + '\nopen Compiler Compiler.CompilationModel\n')
    definition = 'def activeModel : CompilationModel := imported.model\n'
    if mutation == 'drop-events':
        definition = '''def activeModel : CompilationModel :=
  { imported.model with functions := imported.model.functions.map fun fn =>
      { fn with body := fn.body.filter fun stmt =>
          match stmt with | .emit .. => false | _ => true } }
'''
    driver = directory / 'Model.lean'
    driver.write_text(header + definition)
    probe = directory / 'Snapshot.lean'
    selectors = '[' + ', '.join(str(int(selector(s), 16)) for s in signatures) + ']'
    probe.write_text(driver.read_text() + f'''\n#eval do
  unless modelImportCovered activeModel && imported.report.projections.isEmpty do
    throw (IO.userError "storage snapshot requires covered roots and direct ABI parameters")
  let selectors : List Nat := {selectors}
  let ir ← IO.ofExcept (Compiler.CompilationModel.compile activeModel selectors .cancun)
  let result := Lean.Json.mkObj [
    ("model", Lean.toJson (toString (repr activeModel))),
    ("importedModel", Lean.toJson (toString (repr imported.model))),
    ("report", Lean.toJson imported.report.toText),
    ("digest", Lean.toJson imported.report.sourceDigest),
    ("settings", Lean.toJson imported.report.settingsJson),
    ("contract", Lean.toJson imported.report.contract),
    ("solcLongVersion", Lean.toJson imported.report.solcLongVersion),
    ("solcSha256", Lean.toJson imported.report.solcSha256),
    ("roots", Lean.toJson (activeModel.functions.map (fun (fn : FunctionSpec) => fn.name))),
    ("signatures", Lean.toJson (activeModel.functions.map functionSignature)),
    ("paramCounts", Lean.toJson (activeModel.functions.map (fun (fn : FunctionSpec) => fn.params.length))),
    ("selectors", Lean.toJson selectors),
    ("compilerProof", Lean.toJson (imported.report.functions.map (fun (st : FunctionStatus) => st.compilerProof.toText))),
    ("denoteCovered", Lean.toJson (imported.report.functions.all (fun (st : FunctionStatus) => st.denoteCovered))),
    ("mutation", Lean.toJson {json.dumps(mutation)}),
    ("targetFork", Lean.toJson ("cancun" : String)),
    ("yul", Lean.toJson (Compiler.Yul.render (Compiler.emitYul ir)))]
  IO.println ({json.dumps(SNAPSHOT_MARKER)} ++ result.compress)
''')
    snapshot = eval_json(probe, SNAPSHOT_MARKER)
    validate_snapshot(snapshot, signatures, contract, compiler, mutation)
    write_json(directory / 'snapshot.json', snapshot)
    (directory / 'model.yul').write_text(snapshot['yul'])
    return driver, snapshot


def execute_sequence(driver, input_path, output_path):
    """Bridge the existing Denote adapter through Turbo-Lean, using its unmodified JSON payload."""
    payload = json.loads(input_path.read_text())
    probe = output_path.with_suffix('.eval.lean')
    probe.write_text(driver.read_text() + '\n#eval do\n'
        + f'  let input ← IO.ofExcept (Lean.Json.parse {json.dumps(json.dumps(payload))})\n'
        + '  let result ← IO.ofExcept (Compiler.CompilationModel.SolidityImport.SequenceRunner.execute\n'
        + '    activeModel Compiler.CompilationModel.SolidityImport.Differential.oracle input)\n'
        + f'  IO.println ({json.dumps(SEQUENCE_MARKER)} ++ result.compress)\n')
    rows = eval_json(probe, SEQUENCE_MARKER)
    if not isinstance(rows, list):
        raise HarnessError('actual Denote omitted the sequence array')
    write_json(output_path, rows)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        raise SystemExit('expected MODEL INPUT OUTPUT')
    try:
        execute_sequence(*(Path(s) for s in sys.argv[1:]))
    except (HarnessError, OSError, ValueError) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(2)
