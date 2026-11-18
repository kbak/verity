import Verity.Core.Uint256

/-! Bounded evaluation of EVM word shifts in the executable model. -/

namespace Verity.Core.Uint256

/-- Counts at least 256 discard every input bit, including for the maximum word count. -/
def shlBounded (shift value : Uint256) : Uint256 :=
  if shift.val < 256 then ofNat (value.val <<< shift.val) else 0

/-- The bounded executable shift agrees with the word semantics for every count. -/
theorem shl_eq_bounded : shl = shlBounded := by
  funext shift value
  unfold shlBounded
  split
  · rfl
  · rename_i h
    apply Uint256.ext
    rw [shl, val_ofNat, val_zero, Nat.shiftLeft_eq]
    have divides : 2 ^ 256 ∣ 2 ^ shift.val := Nat.pow_dvd_pow 2 (Nat.le_of_not_gt h)
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd divides _)

end Verity.Core.Uint256
