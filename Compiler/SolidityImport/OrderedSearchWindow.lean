import Compiler.SolidityImport.IntervalSearchProofs

/-! A sufficient entry invariant for a binary search over ordered keys with an
uninitialized prefix. Indices are virtual. A circular array can supply its own physical
lookup and a chronological ordering of its keys. -/

namespace Compiler.CompilationModel.SolidityImport.IntervalSearch

/-- Ordered keys on the initialized suffix of a finite virtual index range. -/
structure OrderedSearchWindow where
  first : Nat
  last : Nat
  target : Nat
  initialized : Nat → Bool
  key : Nat → Nat
  isInitialized : ∀ i, i ≤ last → (initialized i = true ↔ first ≤ i)
  monotone : ∀ i j, first ≤ i → i ≤ j → j ≤ last → key i ≤ key j

/-- Lift a fixed-width key to the ordered interval ending at the reference key. -/
def cyclicKey (modulus reference value : Nat) : Nat :=
  if reference < value then value else value + modulus

/-- Cyclic comparison can use the ordinary order when both keys precede the reference.
In all other cases the lifted keys encode the comparison across one wrap. -/
theorem cyclicKey_le_iff (modulus reference a b : Nat) :
    cyclicKey modulus reference a ≤ cyclicKey modulus reference b ↔
      (if a ≤ reference ∧ b ≤ reference then a ≤ b
       else cyclicKey modulus reference a ≤ cyclicKey modulus reference b) := by
  by_cases both : a ≤ reference ∧ b ≤ reference
  · obtain ⟨ha, hb⟩ := both
    simp only [cyclicKey, Nat.not_lt_of_ge ha, Nat.not_lt_of_ge hb, if_false, ha, hb,
      and_self, if_true, Nat.add_le_add_iff_right]
  · simp only [if_neg both]

/-- For a circular table, all virtual bounds and their sum fit when the caller
supplies the word capacity and the cardinality is within a quarter of it. -/
theorem virtual_endpoints_fit {start count modulus : Nat}
    (inside : start < count) (fits : 4 * count ≤ modulus) :
    (start + count - 1) + (start + count - 1) < modulus := by
  omega

namespace OrderedSearchWindow

/-- Checking adjacent initialized keys suffices for monotonicity over the whole suffix. -/
theorem monotone_of_adjacent {key : Nat → Nat} {first last : Nat}
    (adjacent : ∀ i, first ≤ i → i < last → key i ≤ key (i + 1))
    (i j : Nat) (firstLe : first ≤ i) (ordered : i ≤ j) (bounded : j ≤ last) :
    key i ≤ key j := by
  induction j with
  | zero =>
    have eq : i = 0 := by omega
    rw [eq]
    exact Nat.le_refl _
  | succ j ih =>
    by_cases eq : i = j + 1
    · rw [eq]
      exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) (by omega)) (adjacent j (by omega) (by omega))

/-- Validate initialization flags and neighboring keys on finite virtual rows, then
package the verified order for use at every midpoint. Both checks take one pass. -/
def ofRows? (row : Nat → Bool × Nat) (first last target : Nat) : Option OrderedSearchWindow := do
  if flags : ∀ i : Fin (last + 1), ((row i.val).1 = true ↔ first ≤ i.val) then
    if sorted : ∀ i : Fin last, first ≤ i.val → (row i.val).2 ≤ (row (i.val + 1)).2 then
      return {
        first, last, target
        initialized := fun i => (row i).1
        key := fun i => (row i).2
        isInitialized := fun i hi => flags ⟨i, by omega⟩
        monotone := monotone_of_adjacent (fun i hf hi => sorted ⟨i, hi⟩ hf) }
  none

/-- The adjacent initialized indices enclose the target. A strict upper endpoint
selects one witness even if the program can also exit at an equal neighboring key. -/
def Brackets (w : OrderedSearchWindow) (pivot : Nat) : Prop :=
  w.first ≤ pivot ∧ pivot < w.last ∧
    w.key pivot ≤ w.target ∧ w.target < w.key (pivot + 1)

/-- Inclusive bounds retain the original bracket within the physical lookup domain. -/
def Retains (w : OrderedSearchWindow) (pivot low high : Nat) : Prop :=
  low ≤ pivot ∧ pivot ≤ high ∧ high ≤ w.last

instance (w : OrderedSearchWindow) (pivot : Nat) : Decidable (w.Brackets pivot) := by
  unfold Brackets
  infer_instance

instance (w : OrderedSearchWindow) (pivot low high : Nat) :
    Decidable (w.Retains pivot low high) := by
  unfold Retains
  infer_instance

/-- Exactly the two bound-changing outcomes of one source iteration. An uninitialized
lookup continues immediately, so that case needs no value for the following lookup. -/
def Moves (w : OrderedSearchWindow) (low high nextLow nextHigh : Nat) : Prop :=
  let mid := (low + high) / 2
  ((w.initialized mid = false ∨ (w.key mid ≤ w.target ∧ w.key (mid + 1) < w.target)) ∧
      nextLow = mid + 1 ∧ nextHigh = high) ∨
    ((w.initialized mid = true ∧ w.target < w.key mid) ∧ nextLow = low ∧ nextHigh = mid - 1)

/-- A target between the endpoint keys has an adjacent bracket. -/
theorem exists_brackets (w : OrderedSearchWindow) (ordered : w.first ≤ w.last)
    (atFirst : w.key w.first ≤ w.target) (beforeLast : w.target < w.key w.last) :
    ∃ pivot, w.Brackets pivot := by
  have find (last : Nat) (lo : w.first ≤ last) (hi : w.target < w.key last) :
      ∃ i, w.first ≤ i ∧ i < last ∧ w.key i ≤ w.target ∧ w.target < w.key (i + 1) := by
    induction last with
    | zero =>
      have eq : w.first = 0 := by omega
      rw [← eq] at hi
      omega
    | succ n ih =>
      have ne : w.first ≠ n + 1 := by
        intro h
        rw [← h] at hi
        omega
      have firstLe : w.first ≤ n := by omega
      by_cases atN : w.key n ≤ w.target
      · exact ⟨n, firstLe, Nat.lt_succ_self _, atN, hi⟩
      · obtain ⟨i, h₁, h₂, h₃, h₄⟩ := ih firstLe (by omega)
        exact ⟨i, h₁, by omega, h₃, h₄⟩
  exact find w.last ordered beforeLast

/-- An uninitialized or too-early lookup is strictly below the retained bracket. -/
theorem lt_pivot_of_advance (w : OrderedSearchWindow) {pivot mid : Nat}
    (bracket : w.Brackets pivot) (inRange : mid ≤ w.last)
    (advance : w.initialized mid = false ∨ (w.key mid ≤ w.target ∧ w.key (mid + 1) < w.target)) :
    mid < pivot := by
  obtain ⟨first, last, _, later⟩ := bracket
  rcases advance with empty | ⟨before, nextBefore⟩
  · by_cases initialized : w.first ≤ mid
    · have yes := (w.isInitialized mid inRange).2 initialized
      simp only [empty] at yes
      contradiction
    · omega
  · by_cases equal : mid = pivot
    · subst mid
      omega
    · by_cases after : pivot + 1 ≤ mid
      · have keys := w.monotone (pivot + 1) mid (by omega) after inRange
        omega
      · omega

/-- A lookup later than the target is strictly above the retained bracket. -/
theorem pivot_lt_of_retreat (w : OrderedSearchWindow) {pivot mid : Nat}
    (bracket : w.Brackets pivot) (initialized : w.initialized mid = true)
    (inRange : mid ≤ w.last) (later : w.target < w.key mid) : pivot < mid := by
  obtain ⟨_, last, before, _⟩ := bracket
  have first := (w.isInitialized mid inRange).1 initialized
  by_cases below : mid ≤ pivot
  · have keys := w.monotone mid pivot first below (by omega)
    omega
  · omega

/-- Halving preserves a bracketing index, including early continue and both endpoint updates. -/
theorem progress_of_moves (w : OrderedSearchWindow) {pivot low high nextLow nextHigh : Nat}
    (bracket : w.Brackets pivot) (retains : w.Retains pivot low high)
    (moves : w.Moves low high nextLow nextHigh) :
    w.Retains pivot nextLow nextHigh ∧ nextHigh + 1 - nextLow ≤ (high + 1 - low) / 2 := by
  obtain ⟨left, right, last⟩ := retains
  have midInRange : (low + high) / 2 ≤ w.last := by omega
  have halves := remaining_widths_le_half low high (by omega)
  rcases moves with ⟨advance, rfl, rfl⟩ | ⟨⟨initialized, later⟩, rfl, rfl⟩
  · have below := w.lt_pivot_of_advance bracket midInRange advance
    exact ⟨⟨by omega, right, last⟩, by omega⟩
  · have above := w.pivot_lt_of_retreat bracket initialized midInRange later
    exact ⟨⟨left, by omega, by omega⟩, by omega⟩

/-- A bound on the last virtual index suffices for nonwrapping midpoint arithmetic. -/
theorem midpoint_mod_eq (w : OrderedSearchWindow) {pivot low high modulus : Nat}
    (retains : w.Retains pivot low high) (fits : w.last + w.last < modulus) :
    (low + high) % modulus / 2 = (low + high) / 2 := by
  obtain ⟨left, right, last⟩ := retains
  rw [Nat.mod_eq_of_lt (by omega)]

end OrderedSearchWindow
end Compiler.CompilationModel.SolidityImport.IntervalSearch
