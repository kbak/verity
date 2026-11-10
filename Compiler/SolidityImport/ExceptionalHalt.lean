import Compiler.SolidityImport.Transactions

/-! Exact INVALID observations for the gas-free model. These lemmas concern
termination and rollback; they do not prove a compiler simulation or gas cost. -/
namespace Compiler.CompilationModel.SolidityImport.ExceptionalHalt
open Denote Transactions

/-- The canonical closed instruction passes its metadata identity check. -/
theorem module_beq_self :
    (Compiler.ECM.SolidityInvalid.module == Compiler.ECM.SolidityInvalid.module) = true := by
  simp [BEq.beq, Compiler.ECM.SolidityInvalid.module]
  exact ⟨beq_self_eq_true (some Compiler.ECM.ByteTransport.invalid), rfl, rfl, rfl, rfl⟩

/-- An explicit exceptional halt is not an invented empty REVERT. -/
theorem execute_eq (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) :
    execStmt oracle fields state (.ecm Compiler.ECM.SolidityInvalid.module []) = .invalid := by
  simp only [execStmt, Compiler.ECM.SolidityInvalid.module]
  rfl

/-- Malformed instruction arguments remain an unsupported interpreter outcome. -/
theorem rejects_arguments (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (arg : Expr) (args : List Expr) :
    execStmt oracle fields state (.ecm Compiler.ECM.SolidityInvalid.module (arg :: args)) =
      .revert := by
  simp [execStmt, Compiler.ECM.SolidityInvalid.module]

/-- No statement after INVALID can execute or contribute effects. -/
theorem no_continuation (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (tail : List Stmt) :
    execStmtList oracle fields state (.ecm Compiler.ECM.SolidityInvalid.module [] :: tail) =
      .invalid := by
  simp only [execStmtList, execute_eq]

/-- The complete entry world is restored, including storage, events and accounts. -/
theorem rollback (initial : Verity.ContractState) :
    finishFrame initial .invalid = .ok ⟨false, [], initial, true⟩ := rfl

/-- Code generation emits the exceptional instruction itself. -/
theorem compile_eq : Compiler.ECM.SolidityInvalid.compile [] =
    .ok [.exprStmt (.call "invalid" [])] := rfl

end Compiler.CompilationModel.SolidityImport.ExceptionalHalt
