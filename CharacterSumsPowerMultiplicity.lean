/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsPowerObstruction
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Root multiplicities of rational character correlations

A simple numerator or denominator shift cannot be hidden by a different,
possibly nonreduced polynomial representation of a rational perfect power.
This is the algebraic exceptional-tuple prerequisite for the off-diagonal
character-sum estimate [trevino2012].
-/

public section

namespace SptClassification



/-- Root multiplicity of a nonzero polynomial power. -/
theorem polynomial_rootMultiplicity_pow {F : Type*} [Field F]
    (P : Polynomial F) (a : F) (n : ℕ) (hP : P ≠ 0) :
    Polynomial.rootMultiplicity a (P ^ n) =
      n * Polynomial.rootMultiplicity a P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Polynomial.rootMultiplicity_mul
      (mul_ne_zero (pow_ne_zero n hP) hP), ih]
    simp [Nat.succ_mul, add_comm]

/-- A linear factor occurring once gives root multiplicity one when the
remaining factor does not vanish at the root. -/
theorem polynomial_rootMultiplicity_linear_factor {F : Type*} [Field F]
    (R : Polynomial F) (a : F) (hR : R.eval a ≠ 0) :
    Polynomial.rootMultiplicity a ((Polynomial.X - Polynomial.C a) * R) = 1 := by
  classical
  have hRne : R ≠ 0 := by
    intro hz
    exact hR (by simp [hz])
  have hRmult : Polynomial.rootMultiplicity a R = 0 :=
    Polynomial.rootMultiplicity_eq_zero_iff.mpr (by
      intro hr
      exact (hR hr).elim)
  rw [Polynomial.rootMultiplicity_mul
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero a) hRne)]
  simp [Polynomial.rootMultiplicity_X_sub_C, hRmult]

/-- A polynomial with a nonzero derivative at a root has root multiplicity
exactly one. -/
theorem polynomial_rootMultiplicity_eq_one_of_simple_root
    {F : Type*} [Field F] (P : Polynomial F) (a : F)
    (hroot : P.eval a = 0) (hderiv : P.derivative.eval a ≠ 0) :
    Polynomial.rootMultiplicity a P = 1 := by
  have hdiv : Polynomial.X - Polynomial.C a ∣ P :=
    Polynomial.dvd_iff_isRoot.mpr hroot
  obtain ⟨R, hR⟩ := hdiv
  rw [hR]
  have hEval : R.eval a ≠ 0 := by
    intro hz
    apply hderiv
    rw [hR]
    simp [Polynomial.derivative_mul, Polynomial.eval_mul, hz]
  exact polynomial_rootMultiplicity_linear_factor R a hEval

/-- A simple zero obstructs a cleared rational `n`th-power identity even
when the representing denominator also vanishes there. Requiring the
representing polynomials to be nonzero rules out the meaningless `0/0`
presentation. -/
theorem polynomial_ratio_ne_pow_of_rootMultiplicity_one {F : Type*} [Field F]
    (A B C D : Polynomial F) (a : F) (n : ℕ) (hn : 2 ≤ n)
    (hA : A ≠ 0) (hB : B.eval a ≠ 0)
    (hAmult : Polynomial.rootMultiplicity a A = 1)
    (hC : C ≠ 0) (hD : D ≠ 0) :
    A * D ^ n ≠ B * C ^ n := by
  have hBne : B ≠ 0 := by
    intro hz
    exact hB (by simp [hz])
  have hBmult : Polynomial.rootMultiplicity a B = 0 :=
    Polynomial.rootMultiplicity_eq_zero_iff.mpr (by
      intro hr
      exact (hB hr).elim)
  intro heq
  have hmulA : A * D ^ n ≠ 0 :=
    mul_ne_zero hA (pow_ne_zero n hD)
  have hmulB : B * C ^ n ≠ 0 :=
    mul_ne_zero hBne (pow_ne_zero n hC)
  have hval := congrArg (Polynomial.rootMultiplicity a) heq
  rw [Polynomial.rootMultiplicity_mul hmulA,
    polynomial_rootMultiplicity_pow D a n hD, hAmult,
    Polynomial.rootMultiplicity_mul hmulB,
    polynomial_rootMultiplicity_pow C a n hC, hBmult,
    zero_add] at hval
  have hmod : 1 % n = 0 := by
    calc
      1 % n = (1 + n * Polynomial.rootMultiplicity a D) % n := by
        simp [Nat.add_mod]
      _ = (n * Polynomial.rootMultiplicity a C) % n :=
        congrArg (fun k : ℕ => k % n) hval
      _ = 0 := by simp
  have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  omega

/-- A simple numerator zero absent from the denominator obstructs every
nonzero cleared rational `n`th-power presentation, without a restriction
on whether the candidate denominator vanishes at that point. -/
theorem polynomial_ratio_ne_pow_of_simple_zero_nonzero {F : Type*} [Field F]
    (A B C D : Polynomial F) (a : F) (n : ℕ) (hn : 2 ≤ n)
    (hroot : A.eval a = 0) (hderiv : A.derivative.eval a ≠ 0)
    (hB : B.eval a ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
    A * D ^ n ≠ B * C ^ n := by
  have hA : A ≠ 0 := by
    intro hz
    exact hderiv (by simp [hz])
  exact polynomial_ratio_ne_pow_of_rootMultiplicity_one
    A B C D a n hn hA hB
    (polynomial_rootMultiplicity_eq_one_of_simple_root A a hroot hderiv)
    hC hD

/-- A unique numerator shift, absent from the denominator shifts, gives
a simple zero. It excludes every nonzero polynomial presentation of a
rational perfect power [trevino2012]. -/
theorem shift_product_ratio_ne_pow_of_unique_numerator_nonzero
    {F : Type*} [Field F] {ι κ : Type*} [DecidableEq ι]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (i : ι) (hi : i ∈ s)
    (hunique : ∀ j ∈ s, u j = u i → j = i)
    (habsent : ∀ j ∈ t, v j ≠ u i)
    (n : ℕ) (hn : 2 ≤ n) (C D : Polynomial F)
    (hC : C ≠ 0) (hD : D ≠ 0) :
    (∏ j ∈ s, (Polynomial.X + Polynomial.C (u j))) * D ^ n ≠
      (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))) * C ^ n := by
  obtain ⟨hroot, hsimple⟩ :=
    shift_polynomial_simple_root s u i hi hunique
  have hB :
      (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))).eval (-u i) ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    simpa [sub_eq_add_neg, add_comm] using
      (sub_ne_zero.mpr (habsent j hj))
  exact polynomial_ratio_ne_pow_of_simple_zero_nonzero
    _ _ C D (-u i) n hn hroot hsimple hB hC hD

/-- A unique denominator shift, absent from the numerator shifts, gives
a simple pole and the symmetric rational power obstruction. -/
theorem shift_product_ratio_ne_pow_of_unique_denominator_nonzero
    {F : Type*} [Field F] {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (j : κ) (hj : j ∈ t)
    (hunique : ∀ k ∈ t, v k = v j → k = j)
    (habsent : ∀ i ∈ s, u i ≠ v j)
    (n : ℕ) (hn : 2 ≤ n) (C D : Polynomial F)
    (hC : C ≠ 0) (hD : D ≠ 0) :
    (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) * D ^ n ≠
      (∏ k ∈ t, (Polynomial.X + Polynomial.C (v k))) * C ^ n := by
  intro hpower
  exact shift_product_ratio_ne_pow_of_unique_numerator_nonzero
    t s v u j hj hunique habsent n hn D C hD hC hpower.symm

end SptClassification
