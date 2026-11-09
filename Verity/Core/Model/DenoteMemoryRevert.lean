import Verity.Core.Model.Denote

namespace Compiler.CompilationModel.DenoteMemoryRevert
open Compiler.CompilationModel Denote

/-- Canonical metadata passes the closed-module identity check. -/
theorem module_beq_self :
    (Compiler.ECM.SolidityRevertMemory.module ==
      Compiler.ECM.SolidityRevertMemory.module) = true := by
  simp [BEq.beq, Compiler.ECM.SolidityRevertMemory.module]
  exact ⟨beq_self_eq_true (some Compiler.ECM.ByteTransport.revertMemory),
    rfl, rfl, rfl, rfl⟩

/-- The outcome carries exactly the physical bytes and no committed state. -/
theorem execute_eq (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (args : List Expr) (offset size : Nat)
    (hargs : evalExprList oracle fields state args = some [offset, size]) :
    executeByteRevertMemory oracle fields state Compiler.ECM.SolidityRevertMemory.module args =
      .ok (.revertWithData ((List.range size).map fun i =>
        UInt8.ofNat (state.world.byteMemory.readByte (offset + i)).val)) := by
  simp only [executeByteRevertMemory, hargs, module_beq_self, ↓reduceIte]
  rfl

/-- Code generation preserves the supplied offset and byte length. -/
theorem compile_eq (offset size : Compiler.Yul.YulExpr) :
    Compiler.ECM.SolidityRevertMemory.compile [offset, size] =
      .ok [.exprStmt (.call "revert" [offset, size])] := rfl

end Compiler.CompilationModel.DenoteMemoryRevert
