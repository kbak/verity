"""Checkout-local outputs and faithful warm Lean entrypoint evaluation."""
import json
import os
from pathlib import Path
import subprocess
import sys
import uuid

SUPPLEMENTAL = {
    'packed-memory-hash-routes': ['--require-admission'],
    'bounded-memory': [], 'storage-reference': [], 'storage-reference-routes': [],
    'packed-storage-read': ['--require-composition'], 'tail-cleanup-liveness': [],
    'packed-storage-updates': [], 'packed-storage-rollback': [],
}


def supplemental_command(root, name, attempt, python):
    """Retain stock CI flags; allocate each attempt inside the tested checkout."""
    root = Path(root).resolve()
    output = root / '.lake/verification-output' / attempt / name
    if not output.resolve().is_relative_to(root / '.lake'):
        raise ValueError('Supplemental output escapes the checkout')
    if output.exists():
        raise FileExistsError(f'Preserve the prior attempt: {output}')
    return [python, '-m', 'solidity_differential.check_' + name.replace('-', '_'),
            '--prepared', *SUPPLEMENTAL[name], '--output', str(output)]


def lean_string(value):
    # Lean accepts literal Unicode, but JSON's \uXXXX escapes are not Lean escapes.
    return json.dumps(value, ensure_ascii=False)


def main_driver(source, args):
    """Handle all four Lean --run entrypoint types without masking a nonzero result."""
    namespace = 'VerityWarmMain' + uuid.uuid4().hex
    adapter = '''
namespace NAMESPACE
class Entrypoint (α : Type) where
  run : α → List String → IO Unit
def finish (action : IO UInt32) : IO Unit := do
  let code ← action
  unless code == 0 do throw (IO.userError s!"driver exited {code}")
instance : Entrypoint (IO Unit) where
  run action _ := action
instance : Entrypoint (IO UInt32) where
  run action _ := finish action
instance : Entrypoint (List String → IO Unit) where
  run action args := action args
instance : Entrypoint (List String → IO UInt32) where
  run action args := finish (action args)
end NAMESPACE
'''.replace('NAMESPACE', namespace)
    return (source + '\n' + adapter + '\n#eval ' + namespace + '.Entrypoint.run main ['
            + ', '.join(map(lean_string, args)) + ']\n')


def eval_result(result):
    """Emit Lean diagnostics, failing closed on malformed, timed-out or failed evaluations."""
    sys.stderr.write(result.stderr)
    try:
        report = json.loads(result.stdout)
        if not isinstance(report, dict):
            raise ValueError('Expected a JSON object')
    except ValueError:
        sys.stderr.write(result.stdout)
        return result.returncode or 1
    for key, stream in [('stdout', sys.stdout), ('messages', sys.stdout), ('errors', sys.stderr)]:
        values = report.get(key, [])
        if isinstance(values, str):
            values = [values]
        for value in values:
            text = value if isinstance(value, str) else value.get('message', json.dumps(value))
            stream.write(text + ('' if text.endswith('\n') else '\n'))
    failed = (report.get('ok') is not True or report.get('errors')
              or report.get('timed_out') or report.get('crashed'))
    return result.returncode or (1 if failed else 0)


def lake_adapter(args, turbo, lake):
    """Adapt only supported Lean evaluation forms; forward all other Lake arguments intact."""
    if args[:3] == ['env', 'lean', '--run'] and len(args) >= 4:
        source = Path(args[3]).resolve()
        directory = Path.cwd() / '.lake/verification-eval'
        directory.mkdir(parents=True, exist_ok=True)
        driver = directory / (source.stem + '-' + uuid.uuid4().hex + '.lean')
        driver.write_text(main_driver(source.read_text(), args[4:]))
        timeout = 900000
    elif args[:2] == ['env', 'lean'] and len(args) == 3 and not args[2].startswith('-'):
        driver = Path(args[2]).resolve()
        timeout = 180000
    else:
        os.execv(lake, [lake, *args])
    result = subprocess.run([turbo, '--json', 'eval', str(driver), '--project-dir',
                             str(Path.cwd()), '--timeout-ms', str(timeout)],
                            capture_output=True, text=True, timeout=timeout / 1000 + 30)
    return eval_result(result)
