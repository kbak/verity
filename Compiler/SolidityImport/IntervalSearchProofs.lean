import Compiler.SolidityImport.LoopExecution

/-! Arithmetic and finite-exit conditions for inclusive unsigned interval searches. -/

namespace Compiler.CompilationModel.SolidityImport.IntervalSearch
open LoopExecution

/-- When the endpoint sum wraps, its floor midpoint trips the lower endpoint guard. -/
theorem wrapped_midpoint_lt_low {low high modulus : Nat}
    (lowFits : low < modulus) (highFits : high < modulus) (wrap : modulus ≤ low + high) :
    (low + high) % modulus / 2 < low := by
  rw [Nat.mod_eq_sub_mod wrap, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Excluding a nonwrapping floor midpoint leaves at most half the original indices
on either side, including when one side is empty. -/
theorem remaining_widths_le_half (low high : Nat) (ordered : low ≤ high) :
    (low + high) / 2 - low ≤ (high + 1 - low) / 2 ∧
    high - (low + high) / 2 ≤ (high + 1 - low) / 2 := by
  constructor <;> omega

/-- A search with at most `2 ^ bits` candidates reaches a source exit within
`bits + 1` iterations if every continuing step preserves a nonempty valid interval
and halves its size. The caller supplies the invariant on the reachable states. -/
theorem exists_execute_eq_some_of_interval_progress {State Outcome : Type}
    (step : State → Step State Outcome) (valid : State → Prop) (width : State → Nat)
    (nonempty : ∀ s, valid s → 0 < width s)
    (progress : ∀ s t, valid s → step s = .next t →
      valid t ∧ width t ≤ width s / 2)
    (bits : Nat) (s : State) (initial : valid s) (bounded : width s ≤ 2 ^ bits) :
    ∃ result, execute step (bits + 1) s = some result := by
  induction bits generalizing s with
  | zero =>
    cases h : step s with
    | halt result => exact ⟨result, by rw [execute, h]⟩
    | next t =>
      have ht := progress s t initial h
      have positive := nonempty t ht.1
      simp only [Nat.pow_zero] at bounded
      omega
  | succ n ih =>
    cases h : step s with
    | halt result => exact ⟨result, by rw [execute, h]⟩
    | next t =>
      have ht := progress s t initial h
      rw [Nat.pow_succ] at bounded
      obtain ⟨result, observed⟩ := ih t ht.1 (by omega)
      exact ⟨result, by rw [execute, h]; exact observed⟩

end Compiler.CompilationModel.SolidityImport.IntervalSearch
