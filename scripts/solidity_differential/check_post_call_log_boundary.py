"""Executable admission controls for append-only, byte-exact external logs."""
import argparse
from pathlib import Path
from .engine import command, write_json

SOURCE = r'''import Verity.Core.Model.RawCalls
open Compiler.CompilationModel Compiler.CompilationModel.ByteExternalCall Verity.Core

def previous : Verity.Event := { name := "caller", args := [7], indexedArgs := [] }
def raw (topics : List Uint256) (bytes : List UInt8) : Verity.Event :=
  { name := "foreign", args := [], indexedArgs := topics,
    rawLog := some { emitter := Address.ofNat 9, topics, data := bytes } }
def initial : Verity.ContractState :=
  { Verity.defaultState with thisAddress := Address.ofNat 3, events := [previous] }
def request : Request :=
  { kind := .call, caller := 3, target := 9, value := 0, calldata := [], gas := 1000000 }
def adversary (entries : List Verity.Event) (failure : Nat) :
    Adversary Verity.ContractState Verity.StorageKey where
  respond := fun req world =>
    if req.kind = .staticcall then .exceptional [] else
    if failure = 1 then .revert [0, 7, 0] [] else
    if failure = 2 then .exceptional [] else
    .success { world with events := entries } [] []
  valid := by
    intro req world
    by_cases h : req.kind = .staticcall
    · simp [h, Response.valid]
    · by_cases h1 : failure = 1
      · simp [h, h1, Response.valid]
      · by_cases h2 : failure = 2
        · simp [h, h1, h2, Response.valid]
        · simp [h, h1, h2, Response.valid]

def main : IO UInt32 := do
  let controls := [
    ("empty-extension", [previous], 0, true),
    ("zero-topics-odd-bytes", [previous, raw [] [0, 7, 0]], 0, true),
    ("four-topics", [previous, raw [0, 1, 2, 3] [8]], 0, true),
    ("missing-prefix", [raw [] []], 0, false),
    ("changed-prefix", [{ previous with args := [8] }], 0, false),
    ("unencoded-child", [previous, previous], 0, false),
    ("too-many-topics", [previous, raw [0, 1, 2, 3, 4] []], 0, false),
    ("child-revert", [], 1, true),
    ("child-invalid", [], 2, true)]
  for (name, entries, failure, admitted) in controls do
    let result := RawCalls.execute (adversary entries failure) request initial
    if result.isOk != admitted then throw (IO.userError s!"wrong admission: {name}")
    if let .ok observed := result then
      let expected := if failure = 0 then entries else initial.events
      unless decide (observed.world.events = expected) do
        throw (IO.userError s!"wrong ordered journal: {name}")
      unless observed.returndata == (if failure = 1 then [0, 7, 0] else []) do
        throw (IO.userError s!"wrong failure buffer: {name}")
    IO.println s!"{name}: passed"
  return 0
'''


def run(output):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    command(['turbo-lean', '--json', 'build', 'Verity.Core.Model.RawCalls', '--project-dir', '.'],
            timeout=1800, log=output / 'build.log')
    driver = output / 'Boundary.lean'
    driver.write_text(SOURCE)
    log = command(['lake', 'env', 'lean', '--run', driver], timeout=180, log=output / 'boundary.log')
    assert log.count(': passed') == 9
    write_json(output / 'results.json', {'passed': True, 'controls': 9})


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    run(**vars(parser.parse_args()))
