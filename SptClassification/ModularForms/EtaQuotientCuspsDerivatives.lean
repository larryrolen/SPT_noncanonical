/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientCuspsEulerGerms
public import SptClassification.QSeries.EtaIntegralCore

/-!
# Simple local values at the width-three cusps

The Euler germ at the cusp one-half has a nonzero linear coefficient, and the
Fricke-related cusp one-third has the reciprocal coefficient. These local
calculations support the cusp divisor of the level-six coordinate in
[rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

open PowerSeries

private theorem etaIntegralCore_coeff_one :
    QSeries.etaIntegralCore.coeff 1 = -1 := by
  have h := congrArg (fun F : PowerSeries ℤ => F.coeff 1)
    QSeries.partitionSeries_mul_etaIntegralCore
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal] at h
  omega

/-- The actual eta Euler product has linear coefficient negative one at
the origin. -/
theorem hasDerivAt_etaEulerProduct_zero :
    HasDerivAt etaEulerProduct (-1) 0 := by
  have h := congrArg (fun F : PowerSeries ℂ => F.coeff 1)
    QSeries.etaIntegralCore_map_eq_taylorSeries
  have hderiv : deriv etaEulerProduct 0 = -1 := by
    simpa [QSeries.etaTaylorSeries_coeff, etaIntegralCore_coeff_one] using h.symm
  rw [← hderiv]
  exact (differentiableAt_etaEulerProduct (by simp)).hasDerivAt

private theorem hasDerivAt_etaEulerProduct_power_zero
    (n : ℕ) (hn : 2 ≤ n) (c : ℂ) :
    HasDerivAt (fun q : ℂ => etaEulerProduct (q ^ n * c)) 0 0 := by
  have hpow : HasDerivAt (fun q : ℂ => q ^ n) 0 0 := by
    have hne : n - 1 ≠ 0 := by omega
    convert (hasDerivAt_id (0 : ℂ)).pow n using 1
    · funext q
      rfl
    · simp [hne]
  have harg : HasDerivAt (fun q : ℂ => q ^ n * c) 0 0 := by
    simpa using hpow.mul_const c
  have hη : HasDerivAt etaEulerProduct (-1) ((0 : ℂ) ^ n * c) := by
    simpa [show n ≠ 0 by omega] using hasDerivAt_etaEulerProduct_zero
  convert hη.comp (0 : ℂ) harg using 1
  · funext q
    rfl
  · ring

/-- At the width-three cusp one-half, the eta quotient's normalized Euler
unit has a nonzero linear term, given by the local phase. -/
theorem hasDerivAt_cuspHalfEulerUnit_zero :
    HasDerivAt cuspHalfEulerUnit
      (-Function.Periodic.qParam 1 (-1 / 3)) 0 := by
  let ζ : ℂ := Function.Periodic.qParam 1 (-1 / 3)
  have h3 : HasDerivAt (fun q : ℂ => etaEulerProduct (q ^ 3)) 0 0 := by
    simpa using hasDerivAt_etaEulerProduct_power_zero 3 (by omega) 1
  have h1 : HasDerivAt (fun q : ℂ => etaEulerProduct (q * ζ)) (-ζ) 0 := by
    have hlinear : HasDerivAt (fun q : ℂ => q * ζ) ζ 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).mul_const ζ
    have hη : HasDerivAt etaEulerProduct (-1) ((0 : ℂ) * ζ) := by
      simpa using hasDerivAt_etaEulerProduct_zero
    convert hη.comp (0 : ℂ) hlinear using 1
    · funext q
      rfl
    · ring
  have h6 : HasDerivAt
      (fun q : ℂ => etaEulerProduct
        (q ^ 6 * Function.Periodic.qParam 1 1)) 0 0 :=
    hasDerivAt_etaEulerProduct_power_zero 6 (by omega) _
  have h2 : HasDerivAt
      (fun q : ℂ => etaEulerProduct
        (q ^ 2 * Function.Periodic.qParam 1 (1 / 3))) 0 0 :=
    hasDerivAt_etaEulerProduct_power_zero 2 (by omega) _
  have h := ((h3.pow 5).mul h1).div (h6.mul (h2.pow 5))
    (by simp [etaEulerProduct_zero])
  convert h using 1
  · funext q
    simpa only [ζ, Pi.pow_apply, Pi.mul_apply, Pi.div_apply] using
      cuspHalfEulerUnit_eq q
  · simp [etaEulerProduct_zero, ζ]

/-- The cusp-one-half germ is unramified in characteristic zero. -/
theorem deriv_cuspHalfEulerUnit_zero_ne_zero :
    deriv cuspHalfEulerUnit 0 ≠ 0 := by
  rw [hasDerivAt_cuspHalfEulerUnit_zero.deriv]
  exact neg_ne_zero.mpr (by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _)

/-- The Fricke-related cusp one-third has the opposite Euler-unit slope. -/
theorem hasDerivAt_cuspThirdEulerUnit_zero :
    HasDerivAt cuspThirdEulerUnit
      (Function.Periodic.qParam 1 (-1 / 3)) 0 := by
  have h := hasDerivAt_cuspHalfEulerUnit_zero.inv
    (by simp [cuspHalfEulerUnit_zero])
  convert h using 1
  · funext q
    simpa only [Pi.inv_apply] using cuspThirdEulerUnit_eq q
  · simp [cuspHalfEulerUnit_zero]

/-- The cusp-one-third germ is also unramified in characteristic zero. -/
theorem deriv_cuspThirdEulerUnit_zero_ne_zero :
    deriv cuspThirdEulerUnit 0 ≠ 0 := by
  rw [hasDerivAt_cuspThirdEulerUnit_zero.deriv]
  unfold Function.Periodic.qParam
  exact Complex.exp_ne_zero _

/-- The actual width-three cusp expression for `t` has a simple local
coordinate at one-half, with its exact leading phase. -/
theorem hasDerivAt_levelSixHalfCuspGerm :
    HasDerivAt (fun q : ℂ => -9 * cuspHalfEulerUnit q)
      (9 * Function.Periodic.qParam 1 (-1 / 3)) 0 := by
  convert hasDerivAt_cuspHalfEulerUnit_zero.const_mul (-9 : ℂ) using 1
  ring

theorem deriv_levelSixHalfCuspGerm_zero_ne_zero :
    deriv (fun q : ℂ => -9 * cuspHalfEulerUnit q) 0 ≠ 0 := by
  rw [hasDerivAt_levelSixHalfCuspGerm.deriv]
  exact mul_ne_zero (by norm_num) (by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _)

/-- The Fricke-related cusp-one-third expression for `t` likewise has a
simple local coordinate, with exact leading phase. -/
theorem hasDerivAt_levelSixThirdCuspGerm :
    HasDerivAt (fun q : ℂ => -8 * cuspThirdEulerUnit q)
      (-8 * Function.Periodic.qParam 1 (-1 / 3)) 0 := by
  convert hasDerivAt_cuspThirdEulerUnit_zero.const_mul (-8 : ℂ) using 1

theorem deriv_levelSixThirdCuspGerm_zero_ne_zero :
    deriv (fun q : ℂ => -8 * cuspThirdEulerUnit q) 0 ≠ 0 := by
  rw [hasDerivAt_levelSixThirdCuspGerm.deriv]
  exact mul_ne_zero (by norm_num) (by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _)

end SptClassification
