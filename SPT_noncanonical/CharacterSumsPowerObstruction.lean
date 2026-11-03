/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Simple roots obstruct perfect powers

The off-diagonal character correlation estimate requires excluding rational
functions that are perfect powers. A simple zero of a polynomial is one
elementary obstruction to its being a nontrivial power [trevino2012].
-/

public section

namespace SptClassification

/-- A polynomial with a simple root cannot be a power of exponent at least
two. This holds in every field characteristic, including the prime residue
fields used for character correlations. -/
theorem polynomial_ne_pow_of_simple_root {F : Type*} [Field F]
    (P : Polynomial F) (a : F) (n : ℕ) (hn : 2 ≤ n)
    (hroot : P.eval a = 0) (hsimple : P.derivative.eval a ≠ 0)
    (Q : Polynomial F) : P ≠ Q ^ n := by
  intro hpower
  have hq : Q.eval a = 0 := by
    have hpow : (Q.eval a) ^ n = 0 := by
      simpa only [hpower, Polynomial.eval_pow] using hroot
    by_contra hq
    exact (pow_ne_zero n hq) hpow
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  apply hsimple
  rw [hpower]
  simp [Polynomial.derivative_pow, Polynomial.eval_mul,
    Polynomial.eval_pow, hq]

/-- A product of shifted linear factors has a simple root when the
corresponding shift occurs exactly once. -/
theorem shift_polynomial_simple_root {F : Type*} [Field F]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → F)
    (i : ι) (hi : i ∈ s)
    (hunique : ∀ j ∈ s, u j = u i → j = i) :
    let P := ∏ j ∈ s, (Polynomial.X + Polynomial.C (u j))
    P.eval (-u i) = 0 ∧ P.derivative.eval (-u i) ≠ 0 := by
  classical
  let factor (j : ι) : Polynomial F := Polynomial.X + Polynomial.C (u j)
  let rest : Polynomial F := ∏ j ∈ s.erase i, factor j
  have hfactor :
      (∏ j ∈ s, factor j) = factor i * rest :=
    (Finset.mul_prod_erase s factor hi).symm
  have hrest : rest.eval (-u i) ≠ 0 := by
    dsimp [rest]
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjne : j ≠ i := (Finset.mem_erase.mp hj).1
    have hjmem : j ∈ s := (Finset.mem_erase.mp hj).2
    have hunequal : u j ≠ u i := by
      intro heq
      exact hjne (hunique j hjmem heq)
    simpa [factor, sub_eq_add_neg, add_comm] using
      (sub_ne_zero.mpr hunequal)
  change (∏ j ∈ s, factor j).eval (-u i) = 0 ∧
    (∏ j ∈ s, factor j).derivative.eval (-u i) ≠ 0
  rw [hfactor]
  constructor
  · simp [factor, Polynomial.eval_mul]
  · simp [Polynomial.derivative_mul, Polynomial.eval_mul,
      factor, hrest]

/-- A unique shifted factor prevents the shift polynomial from being a
nontrivial perfect power. This is the elementary multiplicity obstruction
needed before applying an off-diagonal character-sum estimate [trevino2012]. -/
theorem shift_polynomial_ne_pow_of_unique_shift {F : Type*} [Field F]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι → F)
    (i : ι) (hi : i ∈ s)
    (hunique : ∀ j ∈ s, u j = u i → j = i)
    (n : ℕ) (hn : 2 ≤ n) (Q : Polynomial F) :
    (∏ j ∈ s, (Polynomial.X + Polynomial.C (u j))) ≠ Q ^ n := by
  obtain ⟨hroot, hsimple⟩ :=
    shift_polynomial_simple_root s u i hi hunique
  exact polynomial_ne_pow_of_simple_root _ _ n hn hroot hsimple Q

/-- A rational function with a simple zero at which its denominator is
nonzero cannot be an `n`th power represented by polynomials whose denominator
is also nonzero there. The equality is stated after clearing denominators,
so no choice of a fraction representation is hidden. -/
theorem polynomial_ratio_ne_pow_of_simple_zero {F : Type*} [Field F]
    (A B C D : Polynomial F) (a : F) (n : ℕ) (hn : 2 ≤ n)
    (hA : A.eval a = 0) (hAderiv : A.derivative.eval a ≠ 0)
    (hB : B.eval a ≠ 0) (hD : D.eval a ≠ 0) :
    A * D ^ n ≠ B * C ^ n := by
  intro hpower
  have hCpow : (C.eval a) ^ n = 0 := by
    have heval := congrArg (Polynomial.eval a) hpower
    have hprod : B.eval a * (C.eval a) ^ n = 0 := by
      simpa [Polynomial.eval_mul, Polynomial.eval_pow, hA] using heval.symm
    exact (mul_eq_zero.mp hprod).resolve_left hB
  have hC : C.eval a = 0 := by
    by_contra hc
    exact (pow_ne_zero n hc) hCpow
  have hleft : (A * D ^ n).derivative.eval a ≠ 0 := by
    simpa [Polynomial.derivative_mul, Polynomial.eval_mul,
      Polynomial.eval_pow, hA] using
      mul_ne_zero hAderiv (pow_ne_zero n hD)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hright : (B * C ^ (2 + k)).derivative.eval a = 0 := by
    simp [Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.eval_mul, Polynomial.eval_pow, hC]
  exact hleft ((congrArg (fun P : Polynomial F => P.derivative.eval a)
    hpower).trans hright)

/-- A numerator shift occurring once and absent from the denominator gives
a simple zero of the quotient. Hence it obstructs every cleared `n`th-power
identity whose representing denominator is nonzero at that zero
[trevino2012]. -/
theorem shift_product_ratio_ne_pow_of_unique_numerator
    {F : Type*} [Field F] {ι κ : Type*} [DecidableEq ι]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (i : ι) (hi : i ∈ s)
    (hunique : ∀ j ∈ s, u j = u i → j = i)
    (habsent : ∀ j ∈ t, v j ≠ u i)
    (n : ℕ) (hn : 2 ≤ n) (C D : Polynomial F)
    (hD : D.eval (-u i) ≠ 0) :
    (∏ j ∈ s, (Polynomial.X + Polynomial.C (u j))) * D ^ n ≠
      (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))) * C ^ n := by
  obtain ⟨hroot, hsimple⟩ :=
    shift_polynomial_simple_root s u i hi hunique
  have hdenominator :
      (∏ j ∈ t, (Polynomial.X + Polynomial.C (v j))).eval (-u i) ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    simpa [sub_eq_add_neg, add_comm] using
      (sub_ne_zero.mpr (habsent j hj))
  exact polynomial_ratio_ne_pow_of_simple_zero _ _ C D (-u i) n hn
    hroot hsimple hdenominator hD

/-- The corresponding simple-pole obstruction follows by inverting the
rational function. Its representing numerator must be nonzero at the pole. -/
theorem shift_product_ratio_ne_pow_of_unique_denominator
    {F : Type*} [Field F] {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (u : ι → F) (v : κ → F)
    (j : κ) (hj : j ∈ t)
    (hunique : ∀ k ∈ t, v k = v j → k = j)
    (habsent : ∀ i ∈ s, u i ≠ v j)
    (n : ℕ) (hn : 2 ≤ n) (C D : Polynomial F)
    (hC : C.eval (-v j) ≠ 0) :
    (∏ i ∈ s, (Polynomial.X + Polynomial.C (u i))) * D ^ n ≠
      (∏ k ∈ t, (Polynomial.X + Polynomial.C (v k))) * C ^ n := by
  intro hpower
  exact shift_product_ratio_ne_pow_of_unique_numerator
    t s v u j hj hunique habsent n hn D C hC hpower.symm

end SptClassification
