/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ProgressionLaurent

/-! # Bounds and residue classes in Laurent products

The powered progression in [rolenManuscript, §2] has integral `q`-indices
because its exponent is divisible by the progression modulus.
-/

public section

namespace SptClassification.QSeries

variable {R : Type*} [CommRing R]

/-- Lower bounds add when Laurent series are multiplied. -/
theorem laurent_mul_support_lower (F G : LaurentSeries R) (a b : ℤ)
    (hF : ∀ r, F.coeff r ≠ 0 → a ≤ r)
    (hG : ∀ r, G.coeff r ≠ 0 → b ≤ r) :
    ∀ r, (F * G).coeff r ≠ 0 → a + b ≤ r := by
  intro r hr
  obtain ⟨i, hi, j, hj, hij⟩ := HahnSeries.support_mul_subset hr
  have hi' := hF i hi
  have hj' := hG j hj
  change i + j = r at hij
  omega

/-- Lower bounds multiply by the natural exponent. -/
theorem laurent_pow_support_lower (F : LaurentSeries R) (a : ℤ)
    (hF : ∀ r, F.coeff r ≠ 0 → a ≤ r) (n : ℕ) :
    ∀ r, (F ^ n).coeff r ≠ 0 → (n : ℤ) * a ≤ r := by
  induction n with
  | zero =>
      intro r hr
      by_cases h : r = 0
      · subst r; simp
      · simp [HahnSeries.coeff_one, h] at hr
  | succ n ih =>
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        laurent_mul_support_lower (F ^ n) F ((n : ℤ) * a) a ih hF

/-- Residue classes add under Laurent multiplication. -/
theorem laurent_mul_support_residue (F G : LaurentSeries R) (M : ℕ)
    (a b : ZMod M)
    (hF : ∀ r, F.coeff r ≠ 0 → (r : ZMod M) = a)
    (hG : ∀ r, G.coeff r ≠ 0 → (r : ZMod M) = b) :
    ∀ r, (F * G).coeff r ≠ 0 → (r : ZMod M) = a + b := by
  intro r hr
  obtain ⟨i, hi, j, hj, hij⟩ := HahnSeries.support_mul_subset hr
  change i + j = r at hij
  rw [← hij, Int.cast_add, hF i hi, hG j hj]

/-- A power of a single-residue Laurent series has the multiplied residue. -/
theorem laurent_pow_support_residue (F : LaurentSeries R) (M : ℕ) (a : ZMod M)
    (hF : ∀ r, F.coeff r ≠ 0 → (r : ZMod M) = a) (n : ℕ) :
    ∀ r, (F ^ n).coeff r ≠ 0 → (r : ZMod M) = (n : ZMod M) * a := by
  induction n with
  | zero =>
      intro r hr
      by_cases h : r = 0
      · subst r; simp
      · simp [HahnSeries.coeff_one, h] at hr
  | succ n ih =>
      simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using
        laurent_mul_support_residue (F ^ n) F M ((n : ZMod M) * a) a ih hF

/-- The exact powered progression has support on multiples of its modulus.
No condition on the characteristic or on a reduction prime is needed. -/
theorem progressionLaurent_pow_support (f : ℤ → R) (M : ℕ) (u : ℤ)
    (hbelow : ∃ B : ℤ, ∀ r < B, f r = 0) (n : ℕ) (hn : M ∣ n) :
    ∀ r, (progressionLaurent f M u hbelow ^ n).coeff r ≠ 0 →
      (r : ZMod M) = 0 := by
  have hf : ∀ r, (progressionLaurent f M u hbelow).coeff r ≠ 0 →
      (r : ZMod M) = (u : ZMod M) := by
    intro r hr
    by_contra h
    apply hr
    rw [progressionLaurent_coeff]
    exact progressionRow_eq_zero_of f M u r h
  have hn0 : (n : ZMod M) = 0 := by
    obtain ⟨k, rfl⟩ := hn
    simp
  simpa only [hn0, zero_mul] using
    laurent_pow_support_residue (progressionLaurent f M u hbelow) M u hf n

end SptClassification.QSeries
