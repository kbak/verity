"""Post-callback calldata copies with execution, payment, logs and outer rollback."""
import argparse
import json
from pathlib import Path
from eth_utils import keccak
from .engine import HarnessError, command, write_json
from .check_legacy_raw_calls import campaign, EMPTY
from .check_legacy_void_callbacks import transactions as callback_transactions, ORACLE

FIXTURE = Path('Contracts/SolidityImportSmoke/LegacyPostCallMemoryLoops.sol')
DRIVER = FIXTURE.with_name('LegacyPostCallMemoryLoopsModel.lean')
BASE = FIXTURE.with_name('LegacyVoidCallbacks.sol')


def transactions(seed, caller, accounts, random_cases):
    calls, expected = callback_transactions(seed, caller, accounts, random_cases,
        run_lengths=(0, 1, 31, 32, 33, 65, 129, 257))
    paid = 0
    for tx in calls:
        row = expected[tx['id']]
        if tx['function'] == 'run':
            tx['function'] = 'runCalldata'
            selector = keccak(text='runCalldata(address,uint256,bytes,uint8,bytes,uint256)')[:4]
            tx['data'] = '0x' + selector.hex() + tx['data'][10:]
            if row['status'] == 'ok':
                paid += 3
        # The fixed empty receiver has no child effects. Reverting final callbacks
        # restore the payment too. The callback oracle never observes account balance.
        row['balances'][caller] -= paid
        row['balances'][EMPTY] += paid
    return calls, expected


def check_copy_mutant(out):
    original = (out / 'Driver.lean').read_text()
    marker = 'def model : CompilationModel := imported.model'
    assert original.count(marker) == 1
    replacement = '''private partial def omitCopies : Stmt → Stmt
  | .forEach name _ body => .forEach name (.literal 0) body
  | .ite condition yes no => .ite condition (yes.map omitCopies) (no.map omitCopies)
  | statement => statement

private partial def omitAfterCall (seen : Bool) : List Stmt → List Stmt
  | [] => []
  | statement :: rest =>
      (if seen then omitCopies statement else statement) ::
        omitAfterCall (seen || stmtOpensReentrancyWindow statement) rest

def model : CompilationModel :=
  { imported.model with functions := imported.model.functions.map fun fn =>
      if fn.name == "runCalldata" then { fn with body := omitAfterCall false fn.body } else fn }'''
    inputs = out / 'B' / '1' / 'input.json'
    baseline = json.loads((out / 'B' / '1' / 'output.json').read_text())
    output = out / 'mutant-output.json'
    driver = out / 'Mutant.lean'
    driver.write_text(original.replace(marker, replacement) + '\n#eval main ' +
                      json.dumps([str(inputs), str(output)]) + '\n')
    command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '600000'],
            log=out / 'mutant.log', timeout=630)
    altered = json.loads(output.read_text())
    if len(altered) != len(baseline):
        raise HarnessError('copy mutant omitted observations')
    calls = json.loads((out / 'transactions.json').read_text())
    witnesses, controls = [], []
    for tx, actual, wanted in zip(calls, altered, baseline):
        if tx['function'] != 'runCalldata':
            continue
        # The canonical input header stores its length at the ABI offset in word 2.
        payload = bytes.fromhex(tx['data'][10:])
        offset = int.from_bytes(payload[64:96], 'big')
        length = int.from_bytes(payload[offset:offset + 32], 'big')
        if actual != wanted and length > 0:
            witnesses.append(tx['id'])
        if actual == wanted and length == 0 and wanted['status'] == 'ok':
            controls.append(tx['id'])
    if not witnesses or not controls:
        raise HarnessError('copy mutant needs both a nonempty witness and passing empty-copy control')
    write_json(out / 'mutation.json', {'firstWitness': witnesses[0], 'differences': len(witnesses),
        'passingEmptyControl': controls[0], 'kind': 'omit memory loops after the first interaction in runCalldata'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--optimized', action='store_true')
    args = parser.parse_args()
    out = args.output.resolve()
    result = campaign(out, optimized=args.optimized, seed=7601, random_cases=24,
        fixture=FIXTURE, driver_template=DRIVER,
        extra_sources={BASE.name: BASE.read_text()}, make_transactions=transactions,
        value_transactions=True, oracle_fixture=ORACLE, mock_module='VoidCallMocks',
        mock_program='void-callbacks-v1')
    if result:
        raise HarnessError('post-call memory loop observations differ; see results.json')
    check_copy_mutant(out)
    summary = json.loads((out / 'summary.json').read_text())
    write_json(out / 'complete.json', {**summary, 'mutantsDetected': 1,
        'head': command(['git', 'rev-parse', 'HEAD']).strip(),
        'workingTreeClean': not command(['git', 'status', '--porcelain']).strip()})
    print(f"{summary['count']} post-call memory cases and copy mutation passed")


if __name__ == '__main__':
    main()
