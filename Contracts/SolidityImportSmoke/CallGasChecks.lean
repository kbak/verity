import Verity.Core.Model.CallGasProofs
import Verity.Core.Model.SourceGas

namespace SolidityImportSmoke.CallGasChecks
open Compiler.CompilationModel

private def cold : CallGas.Context :=
  { memoryWords := 3, inputOffset := 2^256 - 1, inputSize := 0,
    targetWarm := false, targetDead := false, transfersValue := false }

theorem cold_capped_call :
    (CallGas.charge 100000 (2^256 - 1) cold).map CallGas.Charged.childGas =
      some 95879 := by decide

theorem stipend_with_zero_operand :
    (CallGas.charge 100000 0 { cold with transfersValue := true }).map
      CallGas.Charged.childGas = some 2300 := by decide

theorem memory_expansion :
    CallGas.opcodeCost { cold with inputOffset := 96, inputSize := 33 } = 2606 := by decide

theorem exact_gas_read : CallGas.observe 2 = some 0 := by decide

theorem exhausted_gas_read : CallGas.observe 1 = none := by decide

theorem unaffordable_call : CallGas.charge 2599 0 cold = none := by decide

theorem delegation_access_charge :
    CallGas.opcodeCost { cold with delegationWarm := some false } = 5200 := by decide

end SolidityImportSmoke.CallGasChecks
