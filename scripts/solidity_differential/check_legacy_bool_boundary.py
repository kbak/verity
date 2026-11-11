"""Executable legacy bool response, scratch-memory and instrumentation boundaries."""
import argparse
from pathlib import Path
from .engine import command, write_json

SOURCE = r'''import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.Differential
import Verity.Core.Model.DenoteByteExternalCalls
open Compiler.CompilationModel Compiler.CompilationModel.Denote Verity.Core

def initial : Verity.ContractState := Id.run do
  let world := { Verity.defaultState with thisAddress := Address.ofNat 3 }
  let world := world.writeAccount (Address.ofNat 9)
    { world.accountWorld (Address.ofNat 9) with code := [0] }
  return (world.writePhysicalMemoryValue 64 128).writePhysicalSlot 7 19

def runCall (state : DenoteState) (mod : Compiler.ECM.ExternalCallModule)
    (selector : Nat := 42) (count : Nat := 1) (args : List Expr := [.literal 9, .literal 8]) :=
  executeLegacyBoolCall SolidityImport.Differential.oracle [] state mod "value" selector count args

def main : IO UInt32 := do
  let canonical := Compiler.ECM.LegacyBoolCall.module "value" 42 1
  for word in [0, 1, 2, 255, 2^255, 2^256-1] do
    for length in [0, 1, 31, 32, 33, 65, 96] do
      let bytes := (List.range length).map fun i =>
        UInt8.ofNat (if i < 32 then word / 256^(31-i) % 256 else 0x53)
      for success in [false, true] do
        let adversary := DenoteByteExternalCalls.staticAdversary fun _ _ =>
          (success, bytes, [.contractSlot 9 0])
        let state : DenoteState := {
          world := initial, bindings := [("kept", 12)],
          byteCallAdversary := some adversary, byteCallGas := some 1000000 }
        let (outcome, touched) ← IO.ofExcept (runCall state canonical)
        unless touched == [.contractSlot 9 0] do throw (IO.userError "lost query accesses")
        match outcome with
        | .continue after =>
            unless success && length >= 32 &&
                after.bindings == bindValue state.bindings "value" (if word == 0 then 0 else 1) &&
                after.rawReturndata == some bytes && (after.world.memory 128).val == word &&
                (after.world.memory 64).val == 128 && (after.world.readSlot 7).val == 19 &&
                (after.world.physicalByte 163).val == 8 &&
                after.byteCallAccesses == touched do throw (IO.userError "legacy bool success differs")
        | .revertWithData data =>
            unless (!success || length < 32) && data == (if success then [] else bytes) do
              throw (IO.userError "legacy bool failure differs")
        | _ => throw (IO.userError "unexpected legacy bool outcome")
        IO.println "response: passed"
  let state : DenoteState := {
    world := initial, bindings := [],
    byteCallAdversary := some (DenoteByteExternalCalls.staticAdversary fun _ _ => (true, [], []))
    byteCallGas := some 1000000 }
  let controls := [
    runCall { state with byteCallAdversary := none } canonical,
    runCall { state with byteCallGas := none } canonical,
    runCall state { canonical with writesState := true },
    runCall state canonical 42 1 [.literal 9],
    runCall state (Compiler.ECM.LegacyBoolCall.module "value" (2^32) 1) (2^32)]
  for result in controls do
    if result.isOk then throw (IO.userError "malformed legacy bool transport admitted")
    IO.println "instrumentation: passed"
  let (outcome, touched) ← IO.ofExcept (runCall state canonical 42 1 [.literal 8, .literal 0])
  match outcome with
  | .revertWithData [] => unless touched.isEmpty do throw (IO.userError "queried empty code")
  | _ => throw (IO.userError "empty-code query did not revert")
  IO.println "empty-code: passed"
  return 0
'''


def run(output):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Differential', '--project-dir', '.'],
            timeout=1800, log=output/'build.log')
    driver = output/'Boundary.lean'
    driver.write_text(SOURCE)
    result = command(['lake', 'env', 'lean', '--run', driver], timeout=180, log=output/'boundary.log')
    assert result.count(': passed') == 90
    write_json(output/'results.json', {'passed': True, 'controls': 90})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    run(parser.parse_args().output)
