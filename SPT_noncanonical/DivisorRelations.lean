/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Algebra.BigOperators.Field

/-!
# Triangular relations indexed by divisors

A homogeneous divisor-sum system with nonzero diagonal coefficients has only the
zero solution. Restricting to a divisor-closed set permits applications to indices
coprime to a fixed modulus.

## Main results

* `eq_zero_of_divisor_relations`: strong-induction elimination of the system.
-/

public section

namespace SptClassification

/-- A homogeneous triangular divisor system has only the zero solution. -/
theorem eq_zero_of_divisor_relations {K : Type*} [Field K]
    (D : Set ℕ) (f : ℕ → K) (c : ℕ → ℕ → K)
    (hD : ∀ m ∈ D, ∀ t, t ∣ m → t ∈ D)
    (hdiag : ∀ m ∈ D, 0 < m → c m m ≠ 0)
    (hrel : ∀ m ∈ D, 0 < m → ∑ t ∈ m.divisors, c m t * f t = 0)
    {m : ℕ} (hm : m ∈ D) (hmpos : 0 < m) : f m = 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hsum : (∑ t ∈ m.divisors, c m t * f t) = c m m * f m := by
      apply Finset.sum_eq_single m
      · intro t ht htm
        have hdiv := (Nat.mem_divisors.mp ht).1
        have htpos : 0 < t := Nat.pos_of_dvd_of_pos hdiv hmpos
        have htlt : t < m := lt_of_le_of_ne (Nat.le_of_dvd hmpos hdiv) htm
        rw [ih t htlt (hD m hm t hdiv) htpos, mul_zero]
      · intro hnot
        exact False.elim (hnot (Nat.mem_divisors.mpr ⟨dvd_refl m, hmpos.ne'⟩))
    exact (mul_eq_zero.mp (hsum.symm.trans (hrel m hm hmpos))).resolve_left
      (hdiag m hm hmpos)

end SptClassification
