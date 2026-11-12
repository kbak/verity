"""Typed source-gas transports require canonical metadata and complete evidence."""
import argparse
from pathlib import Path
from .engine import command, write_json

CHECKS = '''import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.TransportBarriers
import Compiler.SolidityImport.SourceGasRunner
import Compiler.SolidityImport.GasCallMocks
open Compiler Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport
private def expectError (result : Except String α) (expected : String) : IO Unit :=
  match result with
  | .error message => unless message == expected do throw (IO.userError message)
  | .ok _ => throw (IO.userError "unexpectedly accepted")
#eval show IO Unit from do
  let source := ECM.LegacyVoidCall.module 1 [] (some "1:2:0")
  let ordinary := ECM.LegacyVoidCall.module 1 []
  let operands := [Expr.literal 0x3344]
  expectError (ECM.ExternalCallModule.compileCanonical source {} [.lit 0x3344])
    "source gas observations require original bytecode; recompilation unsupported"
  match ECM.ExternalCallModule.compileCanonical ordinary {} [.lit 0x3344] with
  | .ok _ => pure ()
  | .error message => throw (IO.userError message)
  unless source.summaryName == "legacy_void_original_bytecode_gas_evidence" &&
      closedTransportCovered source operands && isClosedVoidCall source do
    throw (IO.userError "canonical callback rejected")
  let forged := { source with writesState := false }
  if closedTransportCovered forged operands || isClosedVoidCall forged then
    throw (IO.userError "forged callback metadata accepted")
  let oracle : DenoteOracle := { mappingSlot := fun _ _ => 0, keccakMemorySlice := fun _ _ _ => 0 }
  let env := GasCallMocks.environment 0x1234 0x1235 0x1236 0x3344
  let state : DenoteState := {
    world := Verity.defaultState
    bindings := []
    byteCallAdversary := env.adversary
    sourceGas := some ⟨100000, [.endFrame 42]⟩ }
  expectError (SourceGasRunner.finish oracle [] state [.ecm ordinary operands])
    "source gas transport requires an explicit call-boundary adapter"
  expectError (SourceGasRunner.finish oracle [] state
    [.ecm (ECM.LegacySignatureCall.recoverModule "result") []])
    "source gas transport requires an explicit call-boundary adapter"
  expectError (executeLegacyVoidCallObserved oracle [] { state with sourceGas := none }
    source 1 [] operands (some "1:2:0")) "original bytecode gas evidence missing"
  match SourceGasRunner.finish oracle [] state [.ecm source operands] with
  | .ok 99958 => pure ()
  | _ => throw (IO.userError "empty-code check consumed a nonexistent GAS/CALL")
  let extra := { state with sourceGas := some ⟨100000, [.read "1:2:0" 0, .endFrame 0]⟩ }
  expectError (SourceGasRunner.finish oracle [] extra [.ecm source operands])
    "unconsumed source gas evidence"
  IO.println "8 typed callback gas boundaries passed"
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
    write_json(out / 'complete.json', {'boundaries': 8})
    print('8 typed callback gas boundaries passed')


if __name__ == '__main__':
    main()
