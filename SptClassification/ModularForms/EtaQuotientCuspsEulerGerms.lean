/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientCuspsThirdExpansion

/-!
# Holomorphic Euler units at the width-three cusps

The Euler expressions for the eta quotient at the cusps one-half and one-third
are units on the open nome disc. In particular, their formulas define genuine
holomorphic cusp germs, as needed for the divisor of the level-six coordinate
in [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

private theorem real_neg_third_cast :
    ((-1 / 3 : ℝ) : ℂ) = -1 / 3 := by norm_num

private theorem real_third_cast :
    ((1 / 3 : ℝ) : ℂ) = 1 / 3 := by norm_num

private theorem norm_qParam_one_real (c : ℝ) :
    ‖Function.Periodic.qParam 1 (c : ℂ)‖ = 1 := by
  unfold Function.Periodic.qParam
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

/-- The Euler expression at the cusp one-half has no zero in its local nome
disc. -/
theorem cuspHalfEulerUnit_ne_zero {q : ℂ} (hq : ‖q‖ < 1) :
    cuspHalfEulerUnit q ≠ 0 := by
  have hpow (n : ℕ) (hn : n ≠ 0) : ‖q ^ n‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hn
  have hscaled (n : ℕ) (hn : n ≠ 0) (c : ℝ) :
      ‖q ^ n * Function.Periodic.qParam 1 (c : ℂ)‖ < 1 := by
    rw [norm_mul, norm_qParam_one_real, mul_one]
    exact hpow n hn
  have hlinear :
      ‖q * Function.Periodic.qParam 1 (-1 / 3)‖ < 1 := by
    simpa only [pow_one, real_neg_third_cast] using
      hscaled 1 (by decide) (-1 / 3)
  have hscaled2 : ‖q ^ 2 * Function.Periodic.qParam 1 (1 / 3)‖ < 1 := by
    simpa only [real_third_cast] using hscaled 2 (by decide) (1 / 3)
  rw [cuspHalfEulerUnit_eq]
  exact div_ne_zero
    (mul_ne_zero (pow_ne_zero _ (etaEulerProduct_ne_zero (hpow 3 (by decide))))
      (etaEulerProduct_ne_zero hlinear))
    (mul_ne_zero (etaEulerProduct_ne_zero (hscaled 6 (by decide) 1))
      (pow_ne_zero _ (etaEulerProduct_ne_zero hscaled2)))

/-- The Euler unit at the cusp one-half is holomorphic throughout the open
nome disc. -/
theorem differentiableAt_cuspHalfEulerUnit {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ cuspHalfEulerUnit q := by
  have hpow (n : ℕ) (hn : n ≠ 0) : ‖q ^ n‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hn
  have hscaled (n : ℕ) (hn : n ≠ 0) (c : ℝ) :
      ‖q ^ n * Function.Periodic.qParam 1 (c : ℂ)‖ < 1 := by
    rw [norm_mul, norm_qParam_one_real, mul_one]
    exact hpow n hn
  have hdiff (n : ℕ) (hn : n ≠ 0) (c : ℝ) :
      DifferentiableAt ℂ
        (fun x : ℂ => etaEulerProduct
          (x ^ n * Function.Periodic.qParam 1 (c : ℂ))) q := by
    have hi : DifferentiableAt ℂ
        (fun x : ℂ => x ^ n * Function.Periodic.qParam 1 (c : ℂ)) q := by
      fun_prop
    exact (differentiableAt_etaEulerProduct (hscaled n hn c)).comp q hi
  have h3 : DifferentiableAt ℂ (fun x : ℂ => etaEulerProduct (x ^ 3)) q := by
    have hi : DifferentiableAt ℂ (fun x : ℂ => x ^ 3) q := by fun_prop
    apply DifferentiableAt.comp (g := etaEulerProduct)
      (f := fun x : ℂ => x ^ 3) (x := q)
    · exact differentiableAt_etaEulerProduct (hpow 3 (by decide))
    · exact hi
  have h1 : DifferentiableAt ℂ
      (fun x : ℂ => etaEulerProduct
        (x * Function.Periodic.qParam 1 (-1 / 3))) q := by
    simpa only [pow_one, real_neg_third_cast] using
      hdiff 1 (by decide) (-1 / 3)
  have hdiff2 : DifferentiableAt ℂ
      (fun x : ℂ => etaEulerProduct
        (x ^ 2 * Function.Periodic.qParam 1 (1 / 3))) q := by
    simpa only [real_third_cast] using hdiff 2 (by decide) (1 / 3)
  have hscaled2 : ‖q ^ 2 * Function.Periodic.qParam 1 (1 / 3)‖ < 1 := by
    simpa only [real_third_cast] using hscaled 2 (by decide) (1 / 3)
  have hfun : cuspHalfEulerUnit =
      (fun x : ℂ =>
        etaEulerProduct (x ^ 3) ^ 5 *
          etaEulerProduct (x * Function.Periodic.qParam 1 (-1 / 3)) /
          (etaEulerProduct (x ^ 6 * Function.Periodic.qParam 1 1) *
            etaEulerProduct (x ^ 2 * Function.Periodic.qParam 1 (1 / 3)) ^ 5)) :=
    funext cuspHalfEulerUnit_eq
  rw [hfun]
  exact ((h3.pow 5).mul h1).div
    ((hdiff 6 (by decide) 1).mul (hdiff2.pow 5))
    (mul_ne_zero (etaEulerProduct_ne_zero (hscaled 6 (by decide) 1))
      (pow_ne_zero _ (etaEulerProduct_ne_zero hscaled2)))

/-- The reciprocal Euler unit at the cusp one-third is holomorphic on its
open nome disc. -/
theorem differentiableAt_cuspThirdEulerUnit {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ cuspThirdEulerUnit q := by
  have hfun : cuspThirdEulerUnit =
      (fun x : ℂ => (cuspHalfEulerUnit x)⁻¹) :=
    funext cuspThirdEulerUnit_eq
  rw [hfun]
  exact (differentiableAt_cuspHalfEulerUnit hq).inv
    (cuspHalfEulerUnit_ne_zero hq)

end SptClassification
