"""Closed source STATICCALL metadata, meter retention and precompile gas boundaries."""
import argparse
import re
from pathlib import Path
from .engine import HarnessError, command, write_json

CHECKS = '''import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.TransportBarriers
import Compiler.SolidityImport.SourceGasRunner
import Compiler.SolidityImport.StaticCallGasFrames
open Compiler Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
#eval show IO Unit from do
  let count ← IO.mkRef 0
  let ensure := fun (condition : Bool) (message : String) => do
    unless condition do throw (IO.userError message)
    count.modify (· + 1)
  let expectError := fun {α : Type} (result : Except String α) (expected : String) => do
    match result with
    | .error message => ensure (message == expected) message
    | .ok _ => throw (IO.userError "unexpectedly accepted")
  for kind in [ECM.LegacyStaticKind.recover, .bytes4 1, .bool 2 1] do
    let mod := ECM.SourceStaticCall.module "result" kind "10:2:0"
    let operands := List.replicate kind.arity (Expr.literal 0x3344)
    expectError (ECM.ExternalCallModule.compileCanonical mod {} [])
      "source gas observations require original bytecode; recompilation unsupported"
    ensure (closedTransportCovered mod operands && isClosedStaticCall mod &&
        mod.summaryName == "legacy_static_original_bytecode_gas_evidence") "canonical rejected"
    let forged := { mod with writesState := true }
    ensure (!(closedTransportCovered forged operands) && !isClosedStaticCall forged)
      "forged metadata admitted"
    expectError (ECM.ExternalCallModule.compileCanonical forged {} [])
      "closed source static call metadata differs"
  let oracle : DenoteOracle := { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 }
  let adversary : ByteExternalCall.Adversary Verity.ContractState Verity.StorageKey := {
    respond := fun _ _ => .revert [] []
    valid := by intros; trivial }
  let state : DenoteState := {
    world := Verity.defaultState, bindings := [], byteCallAdversary := some adversary
    sourceGas := some ⟨100000, [.endFrame 42]⟩ }
  for kind in [ECM.LegacyStaticKind.bytes4 1, .bool 2 1] do
    let mod := ECM.SourceStaticCall.module "result" kind "10:2:0"
    let operands := List.replicate kind.arity (Expr.literal 0x3344)
    match SourceGasRunner.finish oracle [] state [.ecm mod operands] with
    | .ok gas => ensure (gas == 99958) "empty-code branch consumed GAS/STATICCALL"
    | .error message => throw (IO.userError message)
    expectError (executeSourceStaticCall oracle [] { state with sourceGas := none }
      mod "result" kind "10:2:0" operands) "original bytecode gas evidence missing"
    let emptySite := ECM.SourceStaticCall.module "result" kind ""
    expectError (executeSourceStaticCall oracle [] state emptySite "result" kind "" operands)
      "source static call site missing"
  let recovering := ECM.SourceStaticCall.module "result" .recover "10:2:0"
  expectError (SourceGasRunner.finish oracle [] state
    [.ecm recovering (List.replicate 4 (.literal 0))])
    "missing or reordered source gas observation"
  expectError (SourceGasRunner.finish oracle [] state
    [.ecm (ECM.LegacySignatureCall.recoverModule "result") []])
    "source gas transport requires an explicit call-boundary adapter"
  ensure (!(closedTransportCovered
    (ECM.SourceStaticCall.module "result" (.bytes4 (2^32)) "site")
    (List.replicate 3 (.literal 0)))) "oversized selector admitted"
  for allowance in [2999, 3000, 3001] do
    let witness : SourceGas.Call := {
      context := { memoryWords := 0, inputOffset := 0, inputSize := 128,
                   targetWarm := true, targetDead := false, transfersValue := false }
      request := { kind := .staticcall, caller := 256, target := 1, value := 0,
                   gas := allowance, calldata := [] }
      allowance, exceptional := allowance < 3000, gasLeft := allowance - 3000
      success := !(allowance < 3000), returndata := [] }
    match SourceGas.checkRecoveryGas witness with
    | .ok _ => count.modify (· + 1)
    | .error message => throw (IO.userError message)
    expectError (SourceGas.checkRecoveryGas { witness with gasLeft := witness.gasLeft + 1 })
      "source recovery gas differs from precompile cost"
    expectError (SourceGas.checkRecoveryGas { witness with success := !witness.success })
      "source recovery gas differs from precompile cost"
  IO.println s!"{← count.get} static gas boundaries passed"
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    driver = out / 'Checks.lean'
    driver.write_text(CHECKS)
    command(['turbo-lean', 'eval', driver, '--project-dir', Path.cwd(), '--timeout-ms', '180000'],
            log=out / 'checks.log', timeout=210)
    counts = re.findall(r'^(\d+) static gas boundaries passed$', (out / 'checks.log').read_text(), re.M)
    if counts != ['30']:
        raise HarnessError('static boundary checks did not all complete: ' + repr(counts))
    write_json(out / 'complete.json', {'boundaries': int(counts[0])})
    print(counts[0] + ' static gas boundaries passed')


if __name__ == '__main__':
    main()
