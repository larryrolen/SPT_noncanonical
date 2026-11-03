/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum

/-!
# The quadratic twist removing negative squares

The coefficient multiplier `(χ(u)² - χ(-1)χ(u))/2` selects precisely those
indices `u` for which `-u` is a quadratic nonresidue. In particular, it annihilates
all negative square indices, including indices divisible by the prime.

## Main definitions

* `negativeSquareSelector`: the rational coefficient multiplier.

## Main results

* `negativeSquareSelector_eq`: its exact indicator-function description.
* `negativeSquareSelector_neg_sq`: negative squares are annihilated.
* `legendreSym_mul_square`: multiplication by a nonzero square preserves the symbol.
-/

public section

namespace SptClassification

/-- The coefficient multiplier of the quadratic twist selecting negative nonresidues. -/
def negativeSquareSelector (p : ℕ) [Fact p.Prime] (u : ℤ) : ℚ :=
  ((legendreSym p u : ℚ) ^ 2 -
    (legendreSym p (-1) : ℚ) * (legendreSym p u : ℚ)) / 2

/-- The three possible integer values of a Legendre symbol. -/
theorem legendreSym_values (p : ℕ) [Fact p.Prime] (u : ℤ) :
    legendreSym p u = 0 ∨ legendreSym p u = 1 ∨ legendreSym p u = -1 := by
  by_cases hu : (u : ZMod p) = 0
  · exact Or.inl ((legendreSym.eq_zero_iff p u).mpr hu)
  · exact Or.inr (legendreSym.eq_one_or_neg_one p hu)

/-- The twist retains precisely the indices whose negatives are nonresidues. -/
theorem negativeSquareSelector_eq (p : ℕ) [Fact p.Prime] (u : ℤ) :
    negativeSquareSelector p u = if legendreSym p (-u) = -1 then 1 else 0 := by
  have hneg : legendreSym p (-u) = legendreSym p (-1) * legendreSym p u := by
    rw [neg_eq_neg_one_mul, legendreSym.mul]
  have hunit : ((-1 : ℤ) : ZMod p) ≠ 0 := by simp
  rcases legendreSym.eq_one_or_neg_one p hunit with he | he <;>
    rcases legendreSym_values p u with hu | hu | hu <;>
    simp [negativeSquareSelector, hneg, he, hu]

/-- Every negative square is removed, whether or not it is a unit modulo the prime. -/
theorem negativeSquareSelector_neg_sq (p : ℕ) [Fact p.Prime] (t : ℤ) :
    negativeSquareSelector p (-(t ^ 2)) = 0 := by
  rw [negativeSquareSelector_eq]
  by_cases ht : (t : ZMod p) = 0
  · have hzero : legendreSym p (t ^ 2) = 0 :=
      (legendreSym.eq_zero_iff p (t ^ 2)).mpr (by simp [ht])
    simp [hzero]
  · simp [legendreSym.sq_one' p ht]

/-- Square multiplication by a unit does not change the Legendre symbol. -/
theorem legendreSym_mul_square (p : ℕ) [Fact p.Prime] {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) (u : ℤ) :
    legendreSym p (a ^ 2 * u) = legendreSym p u := by
  rw [legendreSym.mul, legendreSym.sq_one' p ha, one_mul]

/-- The twist selector is constant on nonzero square orbits. -/
theorem negativeSquareSelector_mul_square (p : ℕ) [Fact p.Prime] {a : ℤ}
    (ha : (a : ZMod p) ≠ 0) (u : ℤ) :
    negativeSquareSelector p (a ^ 2 * u) = negativeSquareSelector p u := by
  simp only [negativeSquareSelector, legendreSym_mul_square p ha]

end SptClassification
