import Compiler.SolidityImport.LegacyMemory
import Compiler.SolidityImport.Coverage
/-! Scalar range laws and the actual ABI cleanup evaluation rule. Range laws
use mathematical integers; they do not prove solc-to-model correspondence.
Existing EVM backend proofs cover the shared SIGNEXTEND primitive. -/
namespace Compiler.CompilationModel.SolidityImport.LegacySignedProofs
open Denote Verity.Core

/-- Two’s-complement truncation, interpreted as a mathematical signed integer. -/
def signedNarrow (half value : Int) : Int := (value + half) % (2 * half) - half

/-- An explicit narrowing cast is value preserving exactly inside the target range. -/
theorem signed_narrow_eq_iff (half value : Int) (positive : 0 < half) :
    signedNarrow half value = value ↔ -half ≤ value ∧ value < half := by
  unfold signedNarrow
  constructor
  · intro equality
    have lo := Int.emod_nonneg (value + half) (by omega : 2 * half ≠ 0)
    have hi := Int.emod_lt_of_pos (value + half) (by omega : 0 < 2 * half)
    omega
  · intro bounds
    rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- The legacy subtraction guard detects every underflow, including the negative minimum. -/
theorem decrease_guard_iff (modulus x magnitude : Int)
    (hx : 0 ≤ x ∧ x < modulus) (hd : 0 < magnitude ∧ magnitude < modulus) :
    (x - magnitude) % modulus < x ↔ magnitude ≤ x := by
  by_cases fits : magnitude ≤ x
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · have shift : (x - magnitude) % modulus =
        (modulus + (x - magnitude)) % modulus := (Int.add_emod_left _ _).symm
    rw [shift, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- The legacy addition guard detects every overflow, including a zero delta. -/
theorem increase_guard_iff (modulus x delta : Int)
    (hx : 0 ≤ x ∧ x < modulus) (hd : 0 ≤ delta ∧ delta < modulus) :
    x ≤ (x + delta) % modulus ↔ x + delta < modulus := by
  by_cases fits : x + delta < modulus
  · rw [Int.emod_eq_of_lt (by omega) fits]
    omega
  · have shift : (x + delta) % modulus =
        (x + delta - modulus) % modulus := (Int.sub_emod_right _ _).symm
    rw [shift, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- The emitted ABI-v1 cleanup evaluates to the shared EVM SIGNEXTEND operation. -/
theorem signed_cleanup_eval (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (expr : Expr) (value bits : Nat)
    (width : 0 < bits ∧ bits < 256 ∧ bits % 8 = 0)
    (evaluated : evalExpr oracle fields state expr = some value) :
    evalExpr oracle fields state (LegacyMemory.cleanScalar (.intN bits) expr) =
      some (Uint256.signextend (Uint256.ofNat (bits / 8 - 1)) (Uint256.ofNat value)).val := by
  have index : bits / 8 - 1 < Uint256.modulus := by
    have bound : bits / 8 ≤ bits := Nat.div_le_self _ _
    have large : 256 < Uint256.modulus := by decide
    omega
  have clean : LegacyMemory.cleanScalar (.intN bits) expr =
      .signextend (.literal (bits / 8 - 1)) expr := by
    simp only [LegacyMemory.cleanScalar, width.1, width.2.1, width.2.2,
      decide_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  rw [clean, evalExpr_signextend_arm, evalExpr_literal_arm, evaluated]
  change some (Uint256.signextend (Uint256.ofNat (wordNormalize (bits / 8 - 1)))
    (Uint256.ofNat value)).val = _
  have normalized : wordNormalize (bits / 8 - 1) = bits / 8 - 1 :=
    Nat.mod_eq_of_lt index
  rw [normalized]
end Compiler.CompilationModel.SolidityImport.LegacySignedProofs
