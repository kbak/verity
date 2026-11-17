import Compiler.SolidityImport.ObservedExecution
import Compiler.SolidityImport.Differential

/-! Downstream adapter boundaries and persistent frame composition. These executable
checks do not assert source correspondence or termination of imported programs. -/
open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport

private def root (body : ControlLowering.Body) : ObservedImport.Root :=
  { control := { params := [], body }, fields := [{ name := "stored", ty := .uint256 }] }

private def requireCheck (condition : Bool) (message : String) : Except String Unit :=
  if condition then .ok () else .error message

private def boundaries : Except String Unit := do
  let params := [Param.mk "signed" (.intN 24), Param.mk "flag" .bool,
    Param.mk "addr" .address, Param.mk "tag" (.bytesN 2)]
  let valid := [2^256 - 1, 1, 2^160 - 1, 65535 * 2^240]
  discard <| ObservedExecution.bindCanonical params valid
  for invalid in [[2^24 - 1, 1, 0, 0], [0, 2, 0, 0], [0, 0, 2^160, 0],
      [0, 0, 0, 1], [2^256, 0, 0, 0], [], valid ++ [0]] do
    requireCheck (ObservedExecution.bindCanonical params invalid).toOption.isNone
      "invalid words admitted"
  let fn : ObservedImport.Function := { name := "run", root := root [ControlFlow.Program.atom .stop] }
  requireCheck (ObservedExecution.findRoot { functions := [fn] } "other").toOption.isNone
    "wrong root"
  requireCheck (ObservedExecution.findRoot { functions := [fn, fn] } "run").toOption.isNone
    "duplicate"
  requireCheck (ObservedExecution.execute { functions := [fn] } "run" Differential.oracle 20
    { Verity.defaultState with msgValue := 1 } []).toOption.isNone "call value silently discarded"
  requireCheck (ObservedExecution.executeRoot (root []) Differential.oracle 20
    Verity.defaultState []).toOption.isNone "fallthrough became success"
  requireCheck (ObservedExecution.executeRoot
    (root [ControlFlow.Program.atom (.internalCall "missing" [])])
    Differential.oracle 20 Verity.defaultState []).toOption.isNone
    "unsupported evaluation became revert"

private def composition : Except String Unit := do
  let body : ControlLowering.Body := [
    ControlFlow.Program.atom (.setStorage "stored" (.add (.storage "stored") (.literal 1))),
    ControlFlow.Program.atom (.return (.storage "stored"))]
  let slice : ObservedImport.Slice := { functions := [
    { name := "increment", root := root body },
    { name := "fail", root := root (body.take 1 ++ [ControlFlow.Program.atom .revertEmpty]) },
    { name := "invalid", root := root (body.take 1 ++
        [ControlFlow.Program.atom (.ecm Compiler.ECM.SolidityInvalid.module [])]) },
    { name := "spin", root := root (body.take 1 ++
        [.loop [] (.literal 1) [.continueLoop] []]) }] }
  let some first ← ObservedExecution.execute slice "increment" Differential.oracle 100
      Verity.defaultState [] | throw "first call exhausted"
  let some failed ← ObservedExecution.execute slice "fail" Differential.oracle 100 first.world []
    | throw "reverting call exhausted"
  requireCheck (!failed.success && !failed.invalid && failed.data.isEmpty &&
    (failed.world.storage 0).val == 1) "failed frame committed its write"
  let some invalid ←
      ObservedExecution.execute slice "invalid" Differential.oracle 100 first.world []
    | throw "invalid call exhausted"
  requireCheck (!invalid.success && invalid.invalid && (invalid.world.storage 0).val == 1)
    "INVALID lost its distinction or rollback"
  let some last ←
      ObservedExecution.execute slice "increment" Differential.oracle 100 failed.world []
    | throw "following call exhausted"
  requireCheck (first.success && last.success && last.data == Denote.wordBytes 2 &&
    (last.world.storage 0).val == 2) "persistent frame sequence differs"
  for fuel in [0, 1, 100] do
    let outcome ← ObservedExecution.execute slice "spin" Differential.oracle fuel last.world []
    requireCheck outcome.isNone "exhaustion published a source outcome"

private def eventBoundaries : Except String Unit := do
  let definition : EventDef := {
    name := "Notice"
    params := [{ name := "index", ty := .uint16, kind := .indexed }] }
  let emitted := [ControlFlow.Program.atom (.emit "Notice" [.literal 7])]
  let fn := { root (emitted ++ [ControlFlow.Program.atom .stop]) with events := [definition] }
  let world := { Verity.defaultState with thisAddress := Verity.Core.Address.ofNat 4660 }
  let some final ← ObservedExecution.executeRoot fn Differential.oracle 100 world []
    | throw "event frame exhausted"
  let [event] := final.world.events | throw "event journal length differs"
  let some entry := event.rawLog | throw "event has no encoded observation"
  requireCheck (entry.emitter == world.thisAddress && entry.data.isEmpty &&
    entry.topics.map (·.val) == [KeccakEngine.keccak256_str_nat "Notice(uint16)", 7])
    "event topic or emitter differs"
  for definitions in [[], [definition, definition]] do
    requireCheck (ObservedExecution.executeRoot { fn with events := definitions }
      Differential.oracle 100 world []).toOption.isNone "invalid event metadata admitted"
  let some next ← ObservedExecution.executeRoot (root [ControlFlow.Program.atom .stop])
      Differential.oracle 100 final.world [] | throw "following frame exhausted"
  requireCheck next.world.events.isEmpty "previous frame logs leaked"
  let some failed ← ObservedExecution.executeRoot
      { fn with control := {
        fn.control with body := emitted ++ [ControlFlow.Program.atom .revertEmpty] } }
      Differential.oracle 100 world [] | throw "event rollback exhausted"
  requireCheck (!failed.success && failed.world.events.isEmpty) "reverted logs committed"
  let spin := emitted ++ [.loop [] (.literal 1) [.continueLoop] []]
  let outcome ← ObservedExecution.executeRoot
    { fn with control := { fn.control with body := spin } } Differential.oracle 20 world []
  requireCheck outcome.isNone "event exhaustion published a source outcome"

private def rawEventBoundaries : Except String Unit := do
  let entry : Verity.EncodedLog := {
    emitter := Verity.Core.Address.ofNat 42, topics := [7], data := [1, 2, 255] }
  let event : Verity.Event := { name := "", args := [], indexedArgs := [], rawLog := some entry }
  let encoded ← EventObservation.encode (Verity.Core.Address.ofNat 99) [] event
  requireCheck (encoded == entry) "raw opcode log was re-encoded or lost its emitter"
  let bad := { event with rawLog := some { entry with topics := [1, 2, 3, 4, 5] } }
  requireCheck (EventObservation.encode (Verity.Core.Address.ofNat 99) [] bad).toOption.isNone
    "invalid opcode topic count admitted"

/-- Execute the adapter boundaries from a generated smoke driver. -/
def runObservedExecutionChecks : IO Unit := do
  for check in [boundaries, composition, eventBoundaries, rawEventBoundaries] do
    match check with
    | .ok () => pure ()
    | .error message => throw (IO.userError message)
  IO.println "OBSERVED_EXECUTION_CHECKS_OK"
