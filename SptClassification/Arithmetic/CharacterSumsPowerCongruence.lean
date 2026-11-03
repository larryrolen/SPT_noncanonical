/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsPowerMultiplicity

/-!
# Multiplicity congruences for rational character correlations

A rational `n`th power has numerator and denominator root multiplicities
congruent modulo `n`. For products of shifted linear factors, these
multiplicities count occurrences of each shift. This records the precise
exceptional condition behind the higher-moment argument [trevino2012].
-/

public section

namespace SptClassification

/-- Clearing a nonzero rational `n`th-power presentation forces the
numerator and denominator root multiplicities to agree modulo `n`. -/
theorem polynomial_ratio_rootMultiplicity_mod_eq {F : Type*} [Field F]
    (A B C D : Polynomial F) (a : F) (n : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0)
    (hpower : A * D ^ n = B * C ^ n) :
    Polynomial.rootMultiplicity a A % n =
      Polynomial.rootMultiplicity a B % n := by
  have hleft : A * D ^ n ≠ 0 := mul_ne_zero hA (pow_ne_zero n hD)
  have hright : B * C ^ n ≠ 0 := mul_ne_zero hB (pow_ne_zero n hC)
  have hmult := congrArg (Polynomial.rootMultiplicity a) hpower
  rw [Polynomial.rootMultiplicity_mul hleft,
    Polynomial.rootMultiplicity_mul hright,
    polynomial_rootMultiplicity_pow D a n hD,
    polynomial_rootMultiplicity_pow C a n hC] at hmult
  calc
    Polynomial.rootMultiplicity a A % n =
        (Polynomial.rootMultiplicity a A +
          n * Polynomial.rootMultiplicity a D) % n := by simp
    _ = (Polynomial.rootMultiplicity a B +
          n * Polynomial.rootMultiplicity a C) % n :=
      congrArg (fun k : ℕ => k % n) hmult
    _ = Polynomial.rootMultiplicity a B % n := by simp

/-- The root multiplicity of one shifted linear factor is its indicator
for the corresponding shift. -/
theorem rootMultiplicity_shift_factor {F : Type*} [Field F] [DecidableEq F]
    (a b : F) :
    Polynomial.rootMultiplicity (-a) (Polynomial.X + Polynomial.C b) =
      if b = a then 1 else 0 := by
  classical
  by_cases h : b = a
  · subst b
    have hfactor : Polynomial.X + Polynomial.C a =
        Polynomial.X - Polynomial.C (-a) := by simp
    rw [hfactor, Polynomial.rootMultiplicity_X_sub_C]
    simp
  · have hroot : (Polynomial.X + Polynomial.C b).eval (-a) ≠ 0 := by
      simpa [sub_eq_add_neg, add_comm] using (sub_ne_zero.mpr h)
    have hzero :
        Polynomial.rootMultiplicity (-a) (Polynomial.X + Polynomial.C b) = 0 :=
      Polynomial.rootMultiplicity_eq_zero_iff.mpr (by
        intro hr
        exact (hroot hr).elim)
    simp [h, hzero]

/-- A finite product of shifted linear factors is nonzero, even when shifts
repeat. -/
theorem shift_factor_product_ne_zero {F : Type*} [Field F]
    {ι : Type*} (s : Finset ι) (u : ι → F) :
    (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  simpa [sub_eq_add_neg] using
    (Polynomial.X_sub_C_ne_zero (-(u i)))

/-- Root multiplicity of a shifted-factor product counts all occurrences of
the shift, including repetitions. -/
theorem rootMultiplicity_shift_product {F : Type*} [Field F] [DecidableEq F]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → F) (a : F) :
    Polynomial.rootMultiplicity (-a)
      (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) =
      (s.filter (fun i => u i = a)).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfactor : Polynomial.X + Polynomial.C (u i) ≠ 0 := by
      simpa [sub_eq_add_neg] using
        (Polynomial.X_sub_C_ne_zero (-(u i)))
    rw [Finset.prod_insert hi,
      Polynomial.rootMultiplicity_mul
        (mul_ne_zero hfactor (shift_factor_product_ne_zero s u)),
      rootMultiplicity_shift_factor, ih]
    by_cases h : u i = a
    · simp [Finset.filter_insert, h, hi, Finset.mem_filter, add_comm]
    · simp [Finset.filter_insert, h]

/-- A nonzero rational `n`th-power presentation of two products of shifts
forces their occurrence counts at every shift to agree modulo `n`. -/
theorem shift_product_ratio_count_mod_eq {F : Type*} [Field F] [DecidableEq F]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (a : F) (n : ℕ) (C D : Polynomial F)
    (hC : C ≠ 0) (hD : D ≠ 0)
    (hpower :
      (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) * D ^ n =
        (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))) * C ^ n) :
    (s.filter (fun i => u i = a)).card % n =
      (t.filter (fun j => v j = a)).card % n := by
  have hmul := polynomial_ratio_rootMultiplicity_mod_eq
    (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i)))
    (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j)))
    C D (-a) n
    (shift_factor_product_ne_zero s u)
    (shift_factor_product_ne_zero t v)
    hC hD hpower
  simpa only [rootMultiplicity_shift_product] using hmul

end SptClassification
