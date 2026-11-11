"""Executable closed-transport metadata, response and instrumentation controls."""
import argparse
from pathlib import Path
from .engine import command, write_json

SOURCE = r'''import Compiler.SolidityImport.Coverage
import Compiler.SolidityImport.Differential
open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.ByteExternalCall Verity.Core

def responder (failure : Nat) (bytes : List UInt8) :
    Adversary Verity.ContractState Verity.StorageKey where
  respond := fun request world =>
    if request.kind = .staticcall then .exceptional [] else
    if failure = 1 then .revert bytes [.slot 9] else
    if failure = 2 then .exceptional [.slot 9] else
    .success (world.writePhysicalSlot 9 77) bytes [.slot 9]
  valid := by
    intro request world
    by_cases h : request.kind = .staticcall
    · simp [h, Response.valid]
    · by_cases h1 : failure = 1
      · simp [h, h1, Response.valid]
      · by_cases h2 : failure = 2
        · simp [h, h2, Response.valid]
        · simp [h, h1, h2, Response.valid]

def initial : Verity.ContractState := Id.run do
  let world := { Verity.defaultState with thisAddress := Address.ofNat 3 }
  let world := world.writeAccount (Address.ofNat 9)
    { world.accountWorld (Address.ofNat 9) with code := [0] }
  return world.writePhysicalMemoryValue 64 128

def runCall (state : DenoteState) (mod : Compiler.ECM.ExternalCallModule)
    (selector : Nat := 42) (args : List Expr := [.literal 9, .literal 8]) :=
  executeLegacyVoidCall SolidityImport.Differential.oracle [] state mod selector [.word] args

def main : IO UInt32 := do
  let canonical := Compiler.ECM.LegacyVoidCall.module 42 [.word]
  for length in [0, 1, 31, 32, 33, 65] do
    let bytes := (List.range length).map fun i => UInt8.ofNat (i % 3)
    for failure in [0, 1, 2] do
      let state : DenoteState := {
        world := initial, bindings := [("kept", 12)]
        byteCallAdversary := some (responder failure bytes), byteCallGas := some 1000000 }
      let (outcome, touched) ← IO.ofExcept (runCall state canonical)
      unless touched == [.slot 9] do throw (IO.userError "lost child access")
      match outcome with
      | .continue after =>
          unless failure == 0 && after.rawReturndata == some bytes &&
              after.bindings == state.bindings && (after.world.readSlot 9).val == 77 &&
              after.world.thisAddress == state.world.thisAddress &&
              after.byteCallAccesses == [.slot 9] do throw (IO.userError "void success differs")
      | .revertWithData actual =>
          unless failure != 0 && actual == (if failure == 1 then bytes else []) do
            throw (IO.userError "failure bytes differ")
      | _ => throw (IO.userError "unexpected void outcome")
      IO.println s!"response-{failure}-{length}: passed"
  let state : DenoteState := {
    world := initial, bindings := []
    byteCallAdversary := some (responder 0 []), byteCallGas := some 1000000 }
  let controls := [
    ("missing-adversary", runCall { state with byteCallAdversary := none } canonical),
    ("missing-gas", runCall { state with byteCallGas := none } canonical),
    ("metadata", runCall state { canonical with writesState := false }),
    ("arity", runCall state canonical 42 [.literal 9]),
    ("selector", runCall state (Compiler.ECM.LegacyVoidCall.module (2^32) [.word]) (2^32))]
  for (name, result) in controls do
    if result.isOk then throw (IO.userError s!"accepted {name}")
    IO.println s!"{name}: passed"
  let (outcome, touched) ← IO.ofExcept (runCall state canonical 42 [.literal 8, .literal 0])
  match outcome with
  | .revertWithData [] => unless touched.isEmpty do throw (IO.userError "called empty account")
  | _ => throw (IO.userError "missing empty-code revert")
  IO.println "empty-code: passed"
  return 0
'''


def run(output):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Differential', '--project-dir', '.'],
            timeout=1800, log=output / 'build.log')
    driver = output / 'Boundary.lean'
    driver.write_text(SOURCE)
    log = command(['lake', 'env', 'lean', '--run', driver], timeout=180, log=output / 'boundary.log')
    assert log.count(': passed') == 24
    write_json(output / 'results.json', {'passed': True, 'controls': 24})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    run(**vars(parser.parse_args()))
