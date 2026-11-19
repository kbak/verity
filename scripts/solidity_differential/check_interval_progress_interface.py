"""Exercise the proof-requiring command on unguarded interval loops and incomplete frames."""
import argparse
import json
from pathlib import Path

from .engine import HarnessError, command, run_bounded


def checked_driver(output):
    driver = output / 'Check.lean'
    driver.write_text('''import Compiler.SolidityImport.IntervalCommand

open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport Denote CertifiedInterval

solidity_import loopA from "Contracts/SolidityImportSmoke" entry "LegacyLoopControl.sol"
  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,
          optimizerRuns := some 800, bytecodeHash := "none" }
  interval contract LegacyLoopControl
  function search(uint256,uint256,uint256,uint256)
  loop "LegacyLoopControl.sol" line 27 column 9

solidity_import loopB from "Contracts/SolidityImportSmoke" entry "LegacyLoopControl.sol"
  using { solc := "0.7.6+commit.7338295f", evmVersion := "istanbul", viaIR := false,
          optimizerRuns := some 200, bytecodeHash := "none" }
  interval contract LegacyLoopControl
  function search(uint256,uint256,uint256,uint256)
  loop "LegacyLoopControl.sol" line 27 column 9

def frame (bindings : List (String × Nat)) : DenoteState :=
  { world := Verity.defaultState, bindings }
def ready := frame ((loopA.site.lowName, 0) :: (loopA.site.highName, 2) ::
  [("target", 1), ("skipMask", 0)])
def testOracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩

#guard loopA.site.sourceRange == loopB.site.sourceRange
#guard loopA.site.sourceDigest != loopB.site.sourceDigest
#guard loopA.site.framePresent ready
#guard !(loopA.site.framePresent (frame []))
#guard !(loopA.site.framePresent (frame (ready.bindings.filter (·.1 != "target"))))
#guard !(loopA.site.framePresent (frame (ready.bindings.filter (·.1 != "skipMask"))))
#guard !(loopA.site.framePresent (frame ((loopA.site.highName, 2 ^ 256) :: ready.bindings)))
#guard (match loopA.site.step testOracle ready with
  | .halt (.ok (.continue t)) => lookupBinding? t.bindings loopA.site.midName == some 1
  | _ => false)
#guard (match loopA.site.step testOracle (frame []) with | .halt (.error _) => true | _ => false)

example (o : DenoteOracle) (Valid : DenoteState → Prop) (s : DenoteState)
    (p : Progress loopA.site o Valid) (h : Valid s) : True := by
  have _ : Except String StmtOutcome := loopA.site.execute o p s h
  fail_if_success have _ : Except String StmtOutcome := loopA.site.execute o p s
  fail_if_success have _ := loopB.site.execute o p s h
  fail_if_success have _ := loopA.site.execute o (17 : Nat) s h
  fail_if_success have _ := loopA.site.execute o "progress" s h
  fail_if_success have _ := loopA.model
  trivial

example (p : Progress loopA.site testOracle (fun _ => True)) : False :=
  p.supported (frame []) True.intro "missing or invalid interval frame binding" (by rfl)
''')
    evaluate(driver, output / 'check.json')
    wrong_position = output / 'WrongPosition.lean'
    first_import = driver.read_text().split('solidity_import loopB', 1)[0]
    wrong_position.write_text(first_import.replace('line 27 column 9', 'line 27 column 10'))
    evaluate(wrong_position, output / 'wrong-position.json',
             rejection='LegacyLoopControl.sol:27:9: WhileStatement: [solidity-import:unsupported] '
                       'interval search needs progress')


def evaluate(driver, evidence, rejection=None):
    result = run_bounded(['turbo-lean', '--json', 'eval', str(driver),
                          '--project-dir', '.', '--timeout-ms', '90000'])
    report = json.loads(result.stdout)
    evidence.write_text(json.dumps(report, indent=2) + '\n')
    expected = (report.get('ok') if rejection is None else
                not report.get('ok') and any(rejection in e for e in report.get('errors', [])))
    if not expected or report.get('timed_out') or report.get('crashed'):
        raise HarnessError(f'interval proof interface check failed: {report.get("errors")}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    opts = parser.parse_args()
    opts.output.mkdir(parents=True, exist_ok=True)
    command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.IntervalCommand',
             'Compiler.SolidityImport.IntervalHistoryCertificate', 'Compiler.SolidityImport.Differential',
             '--project-dir', '.'], timeout=600)
    checked_driver(opts.output)
    evaluate(Path('Contracts/SolidityImportSmoke/IntervalHistoryChecks.lean'),
             opts.output / 'checked-history.json')
