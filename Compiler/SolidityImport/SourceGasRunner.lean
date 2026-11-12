import Verity.Core.Model.Denote

/-! Retain the source gas cursor across a terminal revert, where the functional
outcome intentionally drops the world. Primitive transitions use canonical
Denote; only conditional/loop sequencing is traversed to retain that cursor.
This is an executable observation adapter, not a compiler equivalence proof. -/
namespace Compiler.CompilationModel.SolidityImport.SourceGasRunner
open Denote

private structure Observed where
  outcome : StmtOutcome
  meter : Option SourceGas.State

mutual
private partial def body (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (statements : List Stmt) : Except String Observed := do
  match statements with
  | [] => pure ⟨.continue state, state.sourceGas⟩
  | head :: tail =>
      let observed ← statement oracle fields state head
      match observed.outcome with
      | .continue next => body oracle fields next tail
      | _ => pure observed

private partial def loop (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name : String) (statements : List Stmt)
    (index remaining : Nat) : Except String Observed := do
  match remaining with
  | 0 => pure ⟨.continue state, state.sourceGas⟩
  | n + 1 =>
      let entered := { state with bindings := bindValue state.bindings name (wordNormalize index) }
      let observed ← body oracle fields entered statements
      match observed.outcome with
      | .continue next => loop oracle fields next name statements (index + 1) n
      | _ => pure observed

private partial def statement (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (stmt : Stmt) : Except String Observed := do
  match stmt with
  | .ite condition yes no =>
      let some condition := evalExpr oracle fields state condition
        | throw "source gas branch evaluation unsupported"
      body oracle fields state (if condition == 0 then no else yes)
  | .forEach name count statements =>
      let some count := evalExpr oracle fields state count
        | throw "source gas loop evaluation unsupported"
      loop oracle fields state name statements 0 count
  | _ =>
      let outcome ← match stmt with
        | .ecm mod args =>
          match mod.byteTransport with
          | some (.sourceGasRead result site) => executeSourceGasRead state mod result site args
          | some (.rawCall result delegated) => do
              let (outcome, _) ← executeRawCall oracle fields state mod result delegated args
              pure outcome
          | some (.log ..) | some (.extCodeSize ..) | some (.extCodeCopy ..)
            | some .invalid | some .revertMemory | some .returnMemory =>
              pure (execStmt oracle fields state stmt)
          | _ => throw "source gas transport requires an explicit call-boundary adapter"
        | .externalCallBind .. | .tryExternalCallBind .. =>
            throw "source gas transport requires an explicit call-boundary adapter"
        | _ => pure (execStmt oracle fields state stmt)
      match outcome with
      | .continue next | .stop next | .return _ next => pure ⟨outcome, next.sourceGas⟩
      | .revertWithData _ | .invalid => pure ⟨outcome, state.sourceGas⟩
      | .revert => throw "source gas execution has unsupported semantics or missing evidence"
end

/-- Verify complete consumption of the original frame's evidence. The ordinary
public/traced runners separately compare the functional outcomes and world. -/
def finish (oracle : DenoteOracle) (fields : List Field) (state : DenoteState)
    (statements : List Stmt) : Except String Nat := do
  let observed ← body oracle fields state statements
  let some meter := observed.meter | throw "original bytecode gas evidence missing"
  SourceGas.finish meter

end Compiler.CompilationModel.SolidityImport.SourceGasRunner
