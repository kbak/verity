import Verity.Core.Model.CallGas

/-! Accounting laws at the original CALL and GAS bytecode boundaries. -/
namespace Compiler.CompilationModel.CallGas

/-- EIP-150 never forwards more than the opcode operand. -/
theorem forwardedGas_le_requested (gas requested : Nat) (ctx : Context) (state : Charged)
    (h : charge gas requested ctx = some state) : state.forwardedGas ≤ requested := by
  by_cases enough : opcodeCost ctx ≤ gas
  · simp only [charge, if_pos enough] at h
    cases h
    exact Nat.min_le_left _ _
  · simp only [charge, if_neg enough] at h
    cases h

/-- Parent overhead, the capped operand and the reserve partition initial gas.
The stipend is deliberately outside this identity. -/
theorem charge_conserves_gas (gas requested : Nat) (ctx : Context) (state : Charged)
    (h : charge gas requested ctx = some state) :
    state.opcodeGas + state.forwardedGas + state.reservedGas = gas := by
  by_cases enough : opcodeCost ctx ≤ gas
  · simp only [charge, if_pos enough] at h
    cases h
    dsimp
    have cap := Nat.min_le_right requested (gas - opcodeCost ctx -
      (gas - opcodeCost ctx) / 64)
    have budget := Nat.sub_le (gas - opcodeCost ctx) ((gas - opcodeCost ctx) / 64)
    omega
  · simp only [charge, if_neg enough] at h
    cases h

/-- GAS observes the post-charge balance, including at the exact two-gas limit. -/
theorem observe_of_enough (gas : Nat) (enough : 2 ≤ gas) :
    observe gas = some (gas - 2) := by
  simp [observe, enough]

/-- Insufficient gas is an absent transition, never a fabricated zero reading. -/
theorem observe_of_insufficient (gas : Nat) (short : gas < 2) :
    observe gas = none := by
  simp [observe, Nat.not_le.mpr short]

/-- An exceptional child returns only the parent's retained reserve. -/
theorem finish_exceptional_zero (state : Charged) :
    finish state true 0 = .ok state.reservedGas := by
  simp [finish]

/-- Oversized gas-return evidence is rejected rather than capped. -/
theorem finish_rejects_excess (state : Charged) (exceptional : Bool) (left : Nat)
    (excess : state.childGas < left) :
    finish state exceptional left = .error "child returned gas above its allowance" := by
  simp [finish, excess]

/-- Ordinary bytecode work reduces the balance by its measured cost. -/
theorem consume_of_enough (gas cost : Nat) (enough : cost ≤ gas) :
    consume gas cost = some (gas - cost) := by
  simp [consume, enough]

/-- Even returning the entire stipend cannot create gas in the parent. -/
theorem returned_gas_le_initial (gas requested left : Nat) (ctx : Context) (state : Charged)
    (charged : charge gas requested ctx = some state) (bound : left ≤ state.childGas) :
    state.reservedGas + left ≤ gas := by
  have partition := charge_conserves_gas gas requested ctx state charged
  have stipend : state.stipend ≤ state.opcodeGas := by
    by_cases enough : opcodeCost ctx ≤ gas
    · simp only [charge, if_pos enough] at charged
      cases charged
      dsimp [opcodeCost]
      split
      · split <;> omega
      · exact Nat.zero_le _
    · simp only [charge, if_neg enough] at charged
      cases charged
  unfold Charged.childGas at bound
  omega

end Compiler.CompilationModel.CallGas
