import Compiler.SolidityImport.ControlFlow
import Verity.Core.Model.Denote

/-! The observed control backend reuses existing scalar statement semantics.
It cannot turn unsupported evaluation or an unfinished loop into a source revert. -/

namespace Compiler.CompilationModel.SolidityImport.ControlDenote
open ControlFlow LoopExecution Denote

/-- Lift a supported leaf outcome, retaining exact source halt distinctions. -/
def leaf (oracle : DenoteOracle) (fields : List Field) (statement : Stmt)
    (state : DenoteState) : Except String (BodyResult DenoteState StmtOutcome) :=
  match execStmt oracle fields state statement with
  | .continue next => .ok (.normal next)
  | .revert => .error "unsupported observed-control leaf evaluation"
  | outcome => .ok (.abrupt outcome)

/-- Conditions use the existing expression semantics, without a fallback Boolean. -/
def test (oracle : DenoteOracle) (fields : List Field) (condition : Expr)
    (state : DenoteState) : Except String (Bool × DenoteState) :=
  match evalExpr oracle fields state condition with
  | some value => .ok (value != 0, state)
  | none => .error "unsupported observed-control condition evaluation"

/-- Evaluate lowered control flow with a global observation budget. No result is
published for exhaustion. Transaction rollback and ABI entry checks remain caller obligations. -/
def observe (oracle : DenoteOracle) (fields : List Field) (fuel : Nat)
    (body : List (Program Stmt Expr)) (state : DenoteState) :
    Option (Except String (Exit DenoteState StmtOutcome)) :=
  ControlFlow.observe (leaf oracle fields) (test oracle fields) fuel body state

end Compiler.CompilationModel.SolidityImport.ControlDenote
