"""Execute gas-accounting mutants against preserved original EVM observations.

The exact CallGas source is evaluated in a fresh namespace, without its theorems,
so changes run even when they invalidate a theorem. No importer rebuild is
needed. Compilation, missing fields and execution errors are never detections.
"""
import argparse
import hashlib
import json
from pathlib import Path

from .engine import HarnessError, command, write_json

MODULE = Path('Verity/Core/Model/CallGas.lean')
MUTANTS = {
    'gas-own-cost': ('some (available - 2)', 'some (available - 1)'),
    'call-eip150-cap': ('remaining / 64', 'remaining / 65'),
    'call-value-stipend': ('then 2300 else 0', 'then 2301 else 0'),
    'call-cold-access': ('then 100 else 2600', 'then 100 else 2599'),
    'call-return-gas': ('state.reservedGas + left', 'state.reservedGas + left + 1'),
    'source-span-cost': ('some (available - cost)', 'some available'),
}
DRIVER = r'''
open Lean Compiler.CompilationModel
private def accounting (input : Json) : Except String Json := do
  let rows ← (← (← input.getObjVal? "transactions").getArr?).toList.mapM fun tx => do
    let ident ← tx.getObjVal? "id"
    let result : Except String Json := do
      let state ← SolidityImport.SourceGasInput.parse (← tx.getObjVal? "sourceGas")
      let mut remaining := state.remaining
      let mut output : List Json := []
      for event in state.events do
        let cost := match event with
          | .read _ cost | .call cost _ | .endFrame cost => cost
        let some after := GasCandidate.consume remaining cost | throw "span OOG"
        remaining := after
        match event with
        | .read _ _ =>
          let some after := GasCandidate.observe remaining | throw "GAS OOG"
          remaining := after
          output := output ++ [Json.mkObj [("kind", toJson "read"), ("remaining", toJson after)]]
        | .call _ witness =>
          let c := witness.context
          let ctx : GasCandidate.Context := {
            memoryWords := c.memoryWords, inputOffset := c.inputOffset, inputSize := c.inputSize
            outputOffset := c.outputOffset, outputSize := c.outputSize
            targetWarm := c.targetWarm, targetDead := c.targetDead
            transfersValue := c.transfersValue, delegationWarm := c.delegationWarm }
          let some charged := GasCandidate.charge remaining witness.request.gas ctx
            | throw "CALL OOG"
          remaining ← GasCandidate.finish charged witness.exceptional witness.gasLeft
          output := output ++ [Json.mkObj [("kind", toJson "call"),
            ("allowance", toJson charged.childGas), ("remaining", toJson remaining)]]
        | .endFrame _ =>
          output := output ++ [Json.mkObj [("kind", toJson "end"), ("remaining", toJson remaining)]]
      return Json.mkObj [("id", ← tx.getObjVal? "id"), ("events", toJson output)]
    return match result with
      | .ok row => row
      | .error reason => Json.mkObj [("id", ident), ("rejected", toJson reason)]
  return toJson rows
private def runAccounting (input output : String) : IO Unit := do
  let parsed ← IO.ofExcept (Json.parse (← IO.FS.readFile input))
  let result ← IO.ofExcept (accounting parsed)
  IO.FS.writeFile output result.compress
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-campaign', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--fixture', type=Path,
                        default=Path('Contracts/SolidityImportSmoke/LegacyGasObservations.sol'))
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    saved = args.source_campaign.resolve()
    source = MODULE.read_text()
    payload = json.loads((saved / 'input.json').read_text())
    expected = json.loads((saved / 'accounting-expected.json').read_text())
    complete = json.loads((saved / 'complete.json').read_text())
    fixture = args.fixture.read_bytes()
    if complete['fixtureSha256'] != hashlib.sha256(fixture).hexdigest():
        raise HarnessError('preserved source differs from fixture')
    if not expected or len(expected) != len(payload['transactions']):
        raise HarnessError('incomplete source accounting observations')
    evidence_files = [saved / f for f in ['input.json', 'accounting-expected.json',
        'complete.json', 'node-provenance.json']]
    evidence_files += sorted((saved / 'node').glob('*.gas.json'))
    if len(evidence_files) != len(expected) + 4:
        raise HarnessError('missing original EVM opcode traces')
    hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in evidence_files}
    write_json(out / 'source-provenance.json', hashes)

    def execute(name, code, transactions):
        folder = out / name
        folder.mkdir()
        write_json(folder / 'input.json', {**payload, 'transactions': transactions})
        # Namespace substitution is the sole transformation in the baseline.
        program = 'import Compiler.SolidityImport.SourceGasInput\n' + code.replace(
            'Compiler.CompilationModel.CallGas', 'Compiler.CompilationModel.GasCandidate') + DRIVER
        program += '\n#eval runAccounting ' + json.dumps(str(folder / 'input.json'))
        program += ' ' + json.dumps(str(folder / 'output.json')) + '\n'
        driver = folder / 'Run.lean'
        driver.write_text(program)
        command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(),
                 '--timeout-ms', '180000'], log=folder / 'execution.log', timeout=210)
        actual = json.loads((folder / 'output.json').read_text())
        if [row['id'] for row in actual] != [tx['id'] for tx in transactions]:
            raise HarnessError('accounting driver dropped/reordered cases')
        for row, tx in zip(actual, transactions):
            if 'rejected' in row:
                if set(row) != {'id', 'rejected'} or not isinstance(row['rejected'], str):
                    raise HarnessError('malformed accounting rejection')
                continue
            if len(row['events']) != len(tx['sourceGas']['events']):
                raise HarnessError('accounting driver omitted events')
            for event in row['events']:
                if set(event) != ({'kind', 'remaining', 'allowance'} if event['kind'] == 'call'
                                  else {'kind', 'remaining'}):
                    raise HarnessError('accounting driver omitted observations')
        return actual

    if execute('baseline', source, payload['transactions']) != expected:
        raise HarnessError('unmodified gas accounting differs from original EVM')
    results = []
    for name, (before, after) in MUTANTS.items():
        if source.count(before) != 1:
            raise HarnessError('nonunique gas mutation anchor: ' + name)
        code = source.replace(before, after)
        actual = execute(name, code, payload['transactions'])
        # A changed allowance can invalidate a later recorded child response.
        # Such model rejections are recorded, never counted as detections.
        witnesses = [i for i, (got, want) in enumerate(zip(actual, expected))
                     if 'rejected' not in got and got != want]
        if not witnesses:
            raise HarnessError('undetected gas mutant: ' + name)
        index = witnesses[0]
        if execute(name + '-witness', code, [payload['transactions'][index]]) != [actual[index]]:
            raise HarnessError('standalone witness changed')
        if execute(name + '-delete', code, []) != []:
            raise HarnessError('empty deletion control differs')
        results.append({'mutant': name, 'detected': True, 'baselinePassed': True,
            'rejectedTraces': [row for row in actual if 'rejected' in row],
            'caseId': expected[index]['id'], 'deletion_minimal': True,
            'sourceSha256': hashlib.sha256(code.encode()).hexdigest(),
            'scope': 'CallGas executable arithmetic versus preserved original EVM; no compiler equivalence'})
    if hashes != {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in evidence_files}:
        raise HarnessError('original evidence changed during replay')
    write_json(out / 'mutation-results.json', results)
    print(f'{len(results)} executable gas mutants detected with standalone witnesses')


if __name__ == '__main__':
    main()
