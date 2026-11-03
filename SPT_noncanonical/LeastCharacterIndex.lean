/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.MinimalDiscriminant
public import SptClassification.Arithmetic.SquareClasses
public import Mathlib.Data.Nat.Find

/-! # Existence and character value of the least discriminant index -/

public section

namespace SptClassification

/-- A positive discriminant index realizes character zero, using the inverse of24. -/
theorem exists_zero_discriminant_character (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ k : ℕ, 1 ≤ k ∧ legendreSym p (1 - 24 * (k : ℤ)) = 0 := by
  have h24 : (24 : ZMod p) ≠ 0 := by
    have hcop := (prime_coprime_twentyFour (Fact.out : p.Prime) hp).symm
    exact ((ZMod.isUnit_iff_coprime 24 p).mpr hcop).ne_zero
  let u : ZMod p := (24 : ZMod p)⁻¹
  refine ⟨u.val + p, by omega, ?_⟩
  apply (legendreSym.eq_zero_iff p _).mpr
  push_cast
  simp [u, mul_inv_cancel₀ h24]

/-- There is a least positive index whose character is not the opposite sign. -/
theorem exists_least_nonopposite_character (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1) :
    ∃ k : ℕ, 1 ≤ k ∧ legendreSym p (1 - 24 * (k : ℤ)) ≠ -sign ∧
      ∀ j : ℕ, 1 ≤ j → j < k → legendreSym p (1 - 24 * (j : ℤ)) = -sign := by
  obtain ⟨j, hj, hzero⟩ := exists_zero_discriminant_character p hp
  have hex : ∃ n : ℕ, 1 ≤ n ∧ legendreSym p (1 - 24 * (n : ℤ)) ≠ -sign := by
    refine ⟨j, hj, ?_⟩
    rw [hzero]
    rcases hsign with rfl | rfl <;> norm_num
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro n hn hnk
  by_contra hne
  exact Nat.find_min hex hnk ⟨hn, hne⟩

/-- Below the prime modulus, a positive discriminant has nonzero character. -/
theorem discriminant_character_ne_zero (p : ℕ) [Fact p.Prime]
    {k : ℕ} (hk : 1 ≤ k) (hbound : 24 * k - 1 < p) :
    legendreSym p (1 - 24 * (k : ℤ)) ≠ 0 := by
  have hpos : 0 < 24 * k - 1 := by omega
  have hcast : (1 : ℤ) - 24 * (k : ℤ) = -((24 * k - 1 : ℕ) : ℤ) := by omega
  intro hzero
  have hz := (legendreSym.eq_zero_iff p _).mp hzero
  rw [hcast] at hz
  simp only [Int.cast_neg, Int.cast_natCast, neg_eq_zero] at hz
  exact (Nat.not_dvd_of_pos_of_lt hpos hbound)
    ((ZMod.natCast_eq_zero_iff (24 * k - 1) p).mp hz)

/-- A nonopposite character below the modulus is exactly the chosen sign. -/
theorem nonopposite_discriminant_character_eq (p : ℕ) [Fact p.Prime]
    {k : ℕ} (hk : 1 ≤ k) (hbound : 24 * k - 1 < p)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1)
    (hne : legendreSym p (1 - 24 * (k : ℤ)) ≠ -sign) :
    legendreSym p (1 - 24 * (k : ℤ)) = sign := by
  have hnonzero := discriminant_character_ne_zero p hk hbound
  have hvalues := legendreSym_values p (1 - 24 * (k : ℤ))
  rcases hsign with rfl | rfl <;> omega

/-- A least nonopposite index below the modulus gives the required squarefree
discriminant and the prescribed nonzero character simultaneously. -/
theorem least_nonopposite_discriminant (p : ℕ) [Fact p.Prime]
    {k : ℕ} (hk : 1 ≤ k) (hbound : 24 * k - 1 < p)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1)
    (hne : legendreSym p (1 - 24 * (k : ℤ)) ≠ -sign)
    (hleast : ∀ j : ℕ, 1 ≤ j → j < k →
      legendreSym p (1 - 24 * (j : ℤ)) = -sign) :
    Squarefree (24 * k - 1) ∧ legendreSym p (1 - 24 * (k : ℤ)) = sign := by
  have hvalue := nonopposite_discriminant_character_eq p hk hbound hsign hne
  exact ⟨least_character_discriminant_squarefree p hk hbound hsign hvalue hleast, hvalue⟩

end SptClassification
