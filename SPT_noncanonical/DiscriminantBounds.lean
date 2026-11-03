/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.LeastCharacterIndex
public import SptClassification.Arithmetic.EffectiveBounds

/-! # Arithmetic consequences of the effective least-index estimate -/

public section

namespace SptClassification

/-- The character-bound estimate for an index puts its discriminant below the
square-root threshold. -/
theorem index_discriminant_lt_sqrt {p k : ℕ} (hp : 10 ^ 11 ≤ p) (hk : 1 ≤ k)
    (hindex : (k : ℝ) ≤ (169 / 50 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) * Real.log p + 1) :
    ((24 * k - 1 : ℕ) : ℝ) + 1 < Real.sqrt (24 * (p : ℝ)) := by
  have hpreal : (10 : ℝ) ^ 11 ≤ p := by exact_mod_cast hp
  have heffective := effective_discriminant_bound hpreal
  have hcast : ((24 * k - 1 : ℕ) : ℝ) = 24 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 24 * k)]
    push_cast
    rfl
  rw [hcast]
  linarith

/-- The same index estimate makes the positive discriminant smaller than the prime. -/
theorem index_discriminant_lt_prime {p k : ℕ} (hp : 10 ^ 11 ≤ p) (hk : 1 ≤ k)
    (hindex : (k : ℝ) ≤ (169 / 50 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) * Real.log p + 1) :
    24 * k - 1 < p := by
  have hroot := index_discriminant_lt_sqrt hp hk hindex
  have hpreal : (1536 : ℝ) < p := by exact_mod_cast (show 1536 < p by omega)
  have hsmall := eight_sqrt_twentyFour_lt hpreal
  have hroot0 := Real.sqrt_nonneg (24 * (p : ℝ))
  have hreal : ((24 * k - 1 : ℕ) : ℝ) < p := by linarith
  exact_mod_cast hreal

/-- Both purely numerical inequalities needed for the geometric obstruction
follow from the effective index estimate. The class-number input will be proved
by counting reduced forms; it is not part of this numerical statement. -/
theorem index_discriminant_obstruction_bounds {p k : ℕ} (hp : 10 ^ 11 ≤ p) (hk : 1 ≤ k)
    (hindex : (k : ℝ) ≤ (169 / 50 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) * Real.log p + 1) :
    (((24 * k - 1 : ℕ) : ℝ) + 1) ^ 2 / 24 < p ∧ 8 * (24 * k - 1) < p := by
  have hroot := index_discriminant_lt_sqrt hp hk hindex
  have hroot0 := Real.sqrt_nonneg (24 * (p : ℝ))
  have hrootsq := Real.sq_sqrt (show 0 ≤ 24 * (p : ℝ) by positivity)
  have hpreal : (1536 : ℝ) < p := by exact_mod_cast (show 1536 < p by omega)
  have hsmall := eight_sqrt_twentyFour_lt hpreal
  constructor
  · nlinarith [mul_pos (show 0 < Real.sqrt (24 * (p : ℝ)) -
        (((24 * k - 1 : ℕ) : ℝ) + 1) by linarith)
      (show 0 < Real.sqrt (24 * (p : ℝ)) +
        (((24 * k - 1 : ℕ) : ℝ) + 1) by positivity)]
  · have hreal : (8 : ℝ) * ((24 * k - 1 : ℕ) : ℝ) < p := by linarith
    exact_mod_cast hreal

/-- A least index satisfying the effective bound gives an actual fundamental
discriminant, its character, residue class, and the two numerical thresholds. -/
theorem effective_least_discriminant (p : ℕ) [Fact p.Prime]
    (hp : 10 ^ 11 ≤ p) {k : ℕ} (hk : 1 ≤ k)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1)
    (hne : legendreSym p (1 - 24 * (k : ℤ)) ≠ -sign)
    (hleast : ∀ j : ℕ, 1 ≤ j → j < k → legendreSym p (1 - 24 * (j : ℤ)) = -sign)
    (hindex : (k : ℝ) ≤ (169 / 50 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) * Real.log p + 1) :
    23 ≤ 24 * k - 1 ∧ (24 * k - 1) % 24 = 23 ∧
      Squarefree (24 * k - 1) ∧ (1 - 24 * (k : ℤ)).IsFundamentalDiscr ∧
      legendreSym p (1 - 24 * (k : ℤ)) = sign ∧
      (((24 * k - 1 : ℕ) : ℝ) + 1) ^ 2 / 24 < p ∧ 8 * (24 * k - 1) < p := by
  have hlt := index_discriminant_lt_prime hp hk hindex
  obtain ⟨hsq, hvalue⟩ := least_nonopposite_discriminant p hk hlt hsign hne hleast
  exact ⟨by omega, by omega, hsq, squarefree_index_discriminant_isFundamental hk hsq,
    hvalue, index_discriminant_obstruction_bounds hp hk hindex⟩

end SptClassification
