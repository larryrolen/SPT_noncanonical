/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.QuadraticTwist
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.FundamentalDiscriminant
import Mathlib.Tactic.Linarith

/-!
# Squarefreeness of a least character discriminant

Removing a square factor from a positive integer congruent to twenty-three modulo
twenty-four preserves that residue class. If the integer is below the character
modulus, the factor is a unit modulo that modulus. A least index with the chosen
nonzero character therefore gives a squarefree discriminant.
-/

public section

namespace SptClassification

/-- Removing a square factor preserves the discriminant residue class modulo24. -/
theorem square_cofactor_mod_twentyFour (u v : ℕ)
    (h : (u * u * v) % 24 = 23) : v % 24 = 23 := by
  have table : ∀ a b : Fin 24,
      (a.val * a.val * b.val) % 24 = 23 → b.val = 23 := by
    decide +kernel
  apply table ⟨u % 24, Nat.mod_lt _ (by decide)⟩ ⟨v % 24, Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.mul_mod, Nat.mod_mod] using h

/-- The least index with a chosen nonzero character gives a squarefree
discriminant whenever that discriminant is smaller than the prime modulus. -/
theorem least_character_discriminant_squarefree (p : ℕ) [Fact p.Prime]
    {k : ℕ} (hk : 1 ≤ k) (hbound : 24 * k - 1 < p)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1)
    (hvalue : legendreSym p (1 - 24 * (k : ℤ)) = sign)
    (hleast : ∀ j : ℕ, 1 ≤ j → j < k →
      legendreSym p (1 - 24 * (j : ℤ)) = -sign) :
    Squarefree (24 * k - 1) := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro u hu hdiv
  obtain ⟨v, hfactor⟩ := hdiv
  have hdpos : 0 < 24 * k - 1 := by omega
  have hdmod : (24 * k - 1) % 24 = 23 := by omega
  have hvmod : v % 24 = 23 :=
    square_cofactor_mod_twentyFour u v (by simpa only [← hfactor] using hdmod)
  have hvpos : 0 < v := by omega
  have hupos : 0 < u := hu.pos
  have hu2 : 2 ≤ u := hu.two_le
  have huSq : 4 ≤ u * u := by nlinarith
  have hvlt : v < 24 * k - 1 := by nlinarith [hfactor]
  have husq_le : u * u ≤ 24 * k - 1 := by
    rw [hfactor]
    exact Nat.le_mul_of_pos_right _ hvpos
  have hult : u < p := by nlinarith
  have hunit : ((u : ℤ) : ZMod p) ≠ 0 := by
    simp only [Int.cast_natCast]
    exact fun hz => (Nat.not_dvd_of_pos_of_lt hupos hult) ((ZMod.natCast_eq_zero_iff u p).mp hz)
  have hfactorInt : (1 : ℤ) - 24 * (k : ℤ) = (u : ℤ) ^ 2 * (-(v : ℤ)) := by
    have hnat : 24 * k = u * u * v + 1 := by omega
    have hcast : (24 : ℤ) * (k : ℤ) = (u : ℤ) * (u : ℤ) * (v : ℤ) + 1 := by
      exact_mod_cast hnat
    nlinarith
  have hvchar : legendreSym p (-(v : ℤ)) = sign := by
    rw [hfactorInt, legendreSym_mul_square p hunit] at hvalue
    exact hvalue
  have hjpos : 1 ≤ (v + 1) / 24 := by omega
  have hjlt : (v + 1) / 24 < k := by omega
  have hjindex : (1 : ℤ) - 24 * (((v + 1) / 24 : ℕ) : ℤ) = -(v : ℤ) := by omega
  have hopposite := hleast ((v + 1) / 24) hjpos hjlt
  rw [hjindex, hvchar] at hopposite
  rcases hsign with rfl | rfl <;> norm_num at hopposite

/-- A squarefree discriminant of the required residue class is fundamental. -/
theorem squarefree_index_discriminant_isFundamental {k : ℕ} (hk : 1 ≤ k)
    (hsq : Squarefree (24 * k - 1)) : (1 - 24 * (k : ℤ)).IsFundamentalDiscr := by
  apply Int.isFundamentalDiscr_iff_squarefree.mpr
  refine Or.inl ⟨by omega, ?_⟩
  apply Int.squarefree_natAbs.mp
  have heq : (1 : ℤ) - 24 * (k : ℤ) = -((24 * k - 1 : ℕ) : ℤ) := by omega
  simpa only [heq, Int.natAbs_neg, Int.natAbs_natCast] using hsq

end SptClassification
