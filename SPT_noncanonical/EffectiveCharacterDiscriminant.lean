/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.DiscriminantBounds
public import SptClassification.Arithmetic.CharacterIntervals
public import SptClassification.QuadraticForms.ClassNumberBound
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Effective discriminants from a conditional character-interval estimate

The character-interval estimate is a quantified input from [trevino2012,
trevino2017]. The arithmetic deductions below follow the normalization in
[rolenManuscript], §5, equation `eq:character`.
-/

public section

namespace SptClassification

variable (p : ℕ) [Fact p.Prime]

/-- The precise constant-interval estimate used in §5 of [rolenManuscript].
Its availability is an explicit input; the character estimate of
[trevino2012, trevino2017] is not proved here. -/
structure CharacterIntervalInput : Prop where
  bound : ∀ (p : ℕ) [Fact p.Prime], Odd p →
    ∀ (χ : DirichletCharacter ℂ p), χ ≠ 1 →
    ∀ (a : ℤ) (H : ℕ), 1 ≤ H →
    ∀ (c : ℂ), c ≠ 0 →
    (∀ j : ℕ, 1 ≤ j → j ≤ H → χ ((a + (j : ℤ)) : ZMod p) = c) →
    (H : ℝ) ≤ (169 / 50 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) * Real.log p

/-- The corrected explicit constant-character bound of
[trevino2017, Theorem 1, p. 1]. The source applies to every odd prime,
every nonprincipal character, and an interval `(a, a + H]`; its
`3.38 = 169/50` bound has no large-prime qualification. The nonzero
constant hypothesis below is a restriction of the source statement.
This literature theorem is used as an admitted premise. -/
theorem corrected_trevino_character_interval_bound
    (q : ℕ) [Fact q.Prime] (hq : Odd q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (a : ℤ) (H : ℕ) (hH : 1 ≤ H)
    (c : ℂ) (hc : c ≠ 0)
    (hconstant : ∀ j : ℕ, 1 ≤ j → j ≤ H →
      χ ((a + (j : ℤ)) : ZMod q) = c) :
    (H : ℝ) ≤ (169 / 50 : ℝ) * (q : ℝ) ^ (1 / 4 : ℝ) * Real.log q := by
  sorry

/-- The corrected Treviño theorem packaged for the effective
discriminant construction. [trevino2017, Theorem 1] -/
theorem correctedTrevinoIntervalInput : CharacterIntervalInput := by
  exact ⟨corrected_trevino_character_interval_bound⟩

/-- The complex-valued quadratic Dirichlet character modulo an odd prime. -/
noncomputable def quadraticDirichletCharacter : DirichletCharacter ℂ p where
  toMonoidHom := (Int.castRingHom ℂ).toMonoidHom.comp
    (quadraticChar (ZMod p)).toMonoidHom
  map_nonunit' := by
    intro a ha
    change ((quadraticChar (ZMod p) a : ℤ) : ℂ) = 0
    exact_mod_cast (quadraticChar (ZMod p)).map_nonunit' a ha

@[simp] theorem quadraticDirichletCharacter_apply (a : ZMod p) :
    quadraticDirichletCharacter p a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := by
  simp [quadraticDirichletCharacter]

theorem quadraticDirichletCharacter_ne_one (hp : 5 ≤ p) :
    quadraticDirichletCharacter p ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ringChar.eq (ZMod p) p]
    omega
  intro h
  apply quadraticChar_ne_one hchar
  ext a
  have ha := congrArg (fun χ : DirichletCharacter ℂ p => χ a) h
  rw [quadraticDirichletCharacter_apply] at ha
  by_cases hunit : IsUnit a
  · simp only [quadraticChar_apply, MulChar.one_apply_coe] at ha ⊢
    exact_mod_cast ha
  · simp only [quadraticChar_apply, MulChar.one_apply_coe] at ha ⊢
    exact_mod_cast ha

/-- The exact Treviño input bounds the first index outside the opposite
quadratic-character class. The interval is obtained by the inverse-of-24
translation, including the nonzero multiplier on its common value. -/
theorem least_character_index_le_of_interval_input (tv : CharacterIntervalInput)
    (hp : 5 ≤ p) {k : ℕ} (hk : 1 ≤ k) {sign : ℤ}
    (hsign : sign = 1 ∨ sign = -1)
    (hprefix : ∀ j : ℕ, 1 ≤ j → j < k →
      legendreSym p (1 - 24 * (j : ℤ)) = -sign) :
    (k : ℝ) ≤ (169 / 50 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) * Real.log p + 1 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hbound_nonneg :
      0 ≤ (169 / 50 : ℝ) * (p : ℝ) ^ (1 / 4 : ℝ) * Real.log p := by
    positivity
  by_cases hk1 : k = 1
  · subst k
    norm_num at *
    linarith
  obtain ⟨start, hconstant⟩ :=
    exists_constant_interval_of_discriminant_prefix p hp hprefix
  have h24 : (24 : ZMod p) ≠ 0 :=
    ((ZMod.isUnit_iff_coprime 24 p).mpr
      (prime_coprime_twentyFour (Fact.out : p.Prime) hp).symm).ne_zero
  have hχ24 : legendreSym p (-24) ≠ 0 := by
    intro hz
    exact (by simpa using h24 : ((-24 : ℤ) : ZMod p) ≠ 0)
      ((legendreSym.eq_zero_iff p _).mp hz)
  have hsign0 : -sign ≠ 0 := by rcases hsign with rfl | rfl <;> norm_num
  let c : ℤ := legendreSym p (-24) * (-sign)
  let a : ℤ := start - 1
  have hc : (c : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero hχ24 hsign0)
  have hinterval : ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 →
      quadraticDirichletCharacter p ((a + (j : ℤ)) : ZMod p) =
        (c : ℂ) := by
    intro j hj hjk
    have hi : j - 1 < k - 1 := by omega
    have hshift : a + (j : ℤ) = start + ((j - 1 : ℕ) : ℤ) := by
      dsimp [a]
      omega
    have hchar := hconstant (j - 1) hi
    rw [← hshift] at hchar
    simpa only [quadraticDirichletCharacter_apply, legendreSym, c, Int.cast_add] using
      congrArg (fun x : ℤ => (x : ℂ)) hchar
  have hlength := tv.bound p hpodd (quadraticDirichletCharacter p)
    (quadraticDirichletCharacter_ne_one p hp) a (k - 1)
    (by omega) c hc hinterval
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [hcast] at hlength
  linarith

/-- The interval estimate yields the actual small fundamental discriminant
needed for the large-prime obstruction in §5 of [rolenManuscript]. The
class-number inequality uses the proper primitive form class number. -/
theorem exists_effective_character_discriminant (tv : CharacterIntervalInput)
    (hp : 10 ^ 11 ≤ p) {sign : ℤ} (hsign : sign = 1 ∨ sign = -1) :
    ∃ d : ℕ, ∃ hd : 23 ≤ d,
      letI : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
      d % 24 = 23 ∧ Squarefree d ∧
        (-(d : ℤ)).IsFundamentalDiscr ∧ ¬ p ∣ 6 * d ∧
        legendreSym p (-(d : ℤ)) = sign ∧
        (d + 1) ^ 2 < 24 * p ∧
        8 * formClassNumber (-(d : ℤ)) < p + 1 := by
  have hp5 : 5 ≤ p := by omega
  obtain ⟨k, hk, hne, hleast⟩ :=
    exists_least_nonopposite_character p hp5 hsign
  have hindex := least_character_index_le_of_interval_input p tv hp5 hk hsign hleast
  obtain ⟨h23, hmod, hsqfree, hfund, hvalue, hnumerical, height⟩ :=
    effective_least_discriminant p hp hk hsign hne hleast hindex
  let d : ℕ := 24 * k - 1
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdlt : d < p := index_discriminant_lt_prime hp hk hindex
  have hcast : (1 : ℤ) - 24 * (k : ℤ) = -(d : ℤ) := by
    dsimp [d]
    omega
  have hpd : ¬ p ∣ d := Nat.not_dvd_of_pos_of_lt hdpos hdlt
  have hp6 : ¬ p ∣ 6 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hp6d : ¬ p ∣ 6 * d := by
    intro h
    rcases (Fact.out : p.Prime).dvd_mul.mp h with h6 | hd
    · exact hp6 h6
    · exact hpd hd
  have hsquare : (d + 1) ^ 2 < 24 * p := by
    have hr : ((d + 1) ^ 2 : ℝ) < 24 * (p : ℝ) := by
      dsimp [d] at hnumerical ⊢
      push_cast at *
      nlinarith
    exact_mod_cast hr
  let hdFact : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
  have hclass : ((@formClassNumber (-(d : ℤ)) hdFact) : ℝ) < d :=
    @formClassNumber_lt_discriminant d hdFact h23
  have hclass_bound : 8 * @formClassNumber (-(d : ℤ)) hdFact < p + 1 := by
    have hr : (8 : ℝ) * ((@formClassNumber (-(d : ℤ)) hdFact) : ℝ) < (p : ℝ) + 1 := by
      have height_real : (8 : ℝ) * (d : ℝ) < p := by exact_mod_cast height
      linarith
    exact_mod_cast hr
  refine ⟨d, h23, hmod, hsqfree, ?_, hp6d, ?_, hsquare, hclass_bound⟩
  · simpa only [hcast] using hfund
  · simpa only [hcast] using hvalue

/-- The large-prime discriminant required in the manuscript, using the
corrected constant-character estimate of [trevino2017, Theorem 1]. The
remaining conclusions are arithmetic deductions from that estimate.
[rolenManuscript, Section 5] -/
theorem exists_large_prime_discriminant
    (hp : 10 ^ 11 ≤ p) {sign : ℤ} (hsign : sign = 1 ∨ sign = -1) :
    ∃ d : ℕ, ∃ hd : 23 ≤ d,
      letI : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
      d % 24 = 23 ∧ Squarefree d ∧
        (-(d : ℤ)).IsFundamentalDiscr ∧ ¬ p ∣ 6 * d ∧
        legendreSym p (-(d : ℤ)) = sign ∧
        (d + 1) ^ 2 < 24 * p ∧
        8 * formClassNumber (-(d : ℤ)) < p + 1 := by
  exact exists_effective_character_discriminant p correctedTrevinoIntervalInput hp hsign

end SptClassification
