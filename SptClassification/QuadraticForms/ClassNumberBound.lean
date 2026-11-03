/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.FormClasses
public import SptClassification.Arithmetic.EffectiveBounds
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Fintype.BigOperators

/-!
# Counting reduced forms

The leading coefficient of a reduced form of discriminant `-d` satisfies
`3a² ≤ d`. For each positive `a`, at most `2a + 1` middle coefficients are
possible, and the discriminant determines the last coefficient uniquely. This
gives the elementary bound for the genuine proper primitive class number.
-/

public section

namespace SptClassification

/-- The exact number of coefficient pairs with `1 ≤ a ≤ A` and `-a ≤ b ≤ a`. -/
theorem reduced_coefficient_choices_card (A : ℕ) :
    Nat.card (Σ a : Fin A, Fin (2 * (a.val + 1) + 1)) = A ^ 2 + 2 * A := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 2 * (i + 1) + 1)]
  induction A with
  | zero => simp
  | succ A ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- A uniform leading-coefficient bound bounds all reduced forms by coefficient pairs. -/
theorem reduced_card_le_coefficient_choices (D : ℤ) (A : ℕ)
    (hA : ∀ Q : ReducedForm D, Q.1.a ≤ A) :
    Nat.card (ReducedForm D) ≤ A ^ 2 + 2 * A := by
  let f : ReducedForm D → Σ a : Fin A, Fin (2 * (a.val + 1) + 1) := fun Q =>
    ⟨⟨Q.1.a.toNat - 1, by have := Q.1.a_pos; have := hA Q; omega⟩,
      ⟨(Q.1.b + Q.1.a).toNat, by
        change (Q.1.b + Q.1.a).toNat < 2 * (Q.1.a.toNat - 1 + 1) + 1
        obtain ⟨hl, hu⟩ := abs_le.mp Q.2.1
        have := Q.1.a_pos
        omega⟩⟩
  have hf : Function.Injective f := by
    intro Q R h
    have ha : Q.1.a = R.1.a := by
      have heq := congrArg (fun s => s.1.val) h
      dsimp [f] at heq
      have := Q.1.a_pos
      have := R.1.a_pos
      omega
    have hb : Q.1.b = R.1.b := by
      have heq := congrArg (fun s => s.2.val) h
      dsimp [f] at heq
      have hQ := abs_le.mp Q.2.1
      have hR := abs_le.mp R.2.1
      omega
    apply Subtype.ext
    apply PositiveForm.ext
    apply BinaryQuadraticForm.ext ha hb
    have hQ := Q.1.discriminant_eq
    have hR := R.1.discriminant_eq
    change Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = D at hQ
    change R.1.b ^ 2 - 4 * R.1.a * R.1.c = D at hR
    rw [← ha, ← hb] at hR
    have hmul : Q.1.a * (Q.1.c - R.1.c) = 0 := by nlinarith only [hQ, hR]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left Q.1.a_pos.ne')
  rw [← reduced_coefficient_choices_card A]
  exact Nat.card_le_card_of_injective f hf

/-- The leading coefficient of a reduced form obeys the sharp elementary square bound. -/
theorem reduced_leading_coefficient_sq_le (d : ℕ) (Q : ReducedForm (-(d : ℤ))) :
    3 * Q.1.a ^ 2 ≤ (d : ℤ) := by
  have hbsq := Q.1.toBinaryQuadraticForm.square_b_le_square_a Q.2.1
  have hac := mul_le_mul_of_nonneg_left Q.2.2 (le_of_lt Q.1.a_pos)
  have hdisc := Q.1.discriminant_eq
  change Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = -(d : ℤ) at hdisc
  nlinarith

theorem reduced_leading_coefficient_le_sqrt (d : ℕ) (Q : ReducedForm (-(d : ℤ))) :
    Q.1.a.toNat ≤ Nat.sqrt (d / 3) := by
  have hsq := reduced_leading_coefficient_sq_le d Q
  have ha : (Q.1.a.toNat : ℤ) = Q.1.a := Int.toNat_of_nonneg (le_of_lt Q.1.a_pos)
  rw [← ha] at hsq
  have hn : 3 * Q.1.a.toNat ^ 2 ≤ d := by exact_mod_cast hsq
  apply Nat.le_sqrt.mpr
  rw [← pow_two]
  omega

/-- An exact integer bound for the proper class number of a negative discriminant. -/
theorem formClassNumber_le_sqrt_bound (d : ℕ) [Fact (-(d : ℤ) < 0)] :
    formClassNumber (-(d : ℤ)) ≤ Nat.sqrt (d / 3) ^ 2 + 2 * Nat.sqrt (d / 3) := by
  apply (formClassNumber_le_reduced_card (-(d : ℤ))).trans
  apply reduced_card_le_coefficient_choices
  intro Q
  have h := reduced_leading_coefficient_le_sqrt d Q
  have ha := Q.1.a_pos
  omega

/-- The classical elementary real upper bound obtained by counting reduced forms. -/
theorem formClassNumber_le_discriminant_bound (d : ℕ) [Fact (-(d : ℤ) < 0)] :
    (formClassNumber (-(d : ℤ)) : ℝ) ≤ (d : ℝ) / 3 + 2 * Real.sqrt ((d : ℝ) / 3) := by
  let A := Nat.sqrt (d / 3)
  have hsq : A * A ≤ d / 3 := Nat.sqrt_le (d / 3)
  have hthree : 3 * (A * A) ≤ d := by omega
  have hsreal : (A : ℝ) ^ 2 ≤ (d : ℝ) / 3 := by
    have hcast : (3 : ℝ) * ((A : ℝ) * A) ≤ d := by exact_mod_cast hthree
    nlinarith
  have hroot : (A : ℝ) ≤ Real.sqrt ((d : ℝ) / 3) :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr hsreal
  have hcount : (formClassNumber (-(d : ℤ)) : ℝ) ≤ (A : ℝ) ^ 2 + 2 * A := by
    exact_mod_cast formClassNumber_le_sqrt_bound d
  linarith

/-- For the manuscript's discriminants, the proper class number is smaller than `d`. -/
theorem formClassNumber_lt_discriminant (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 23 ≤ d) :
    (formClassNumber (-(d : ℤ)) : ℝ) < d :=
  (formClassNumber_le_discriminant_bound d).trans_lt
    (reduced_form_bound_lt_discriminant (by exact_mod_cast hd))

/-- The complete source chain of inequalities for the proper class number. -/
theorem formClassNumber_bound (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 23 ≤ d) :
    (formClassNumber (-(d : ℤ)) : ℝ) ≤ (d : ℝ) / 3 + 2 * Real.sqrt ((d : ℝ) / 3) ∧
      (d : ℝ) / 3 + 2 * Real.sqrt ((d : ℝ) / 3) < d :=
  ⟨formClassNumber_le_discriminant_bound d,
    reduced_form_bound_lt_discriminant (by exact_mod_cast hd)⟩

end SptClassification
