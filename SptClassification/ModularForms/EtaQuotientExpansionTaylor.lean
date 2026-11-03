/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansionFourier
public import SptClassification.QSeries.ConvergentPowers
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Integral Taylor coefficients of the level-six Euler unit

The normalized eta quotient satisfies `q t(τ) = U(q)`.  Its analytic Euler
unit has integral Taylor coefficients because each rescaled Euler factor has
the integral eta core as its coefficient series.  This is a cusp-expansion
prerequisite for the integral coordinate of [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

open PowerSeries

/-- The rescaled integral Euler core has constant coefficient one. -/
theorem etaEulerCoreAtScale_constantCoeff (n : ℕ) :
    constantCoeff (etaEulerCoreAtScale n) = 1 := by
  have h : QSeries.etaIntegralCore.coeff 0 = 1 := by
    rw [← etaEulerSeries_one_eq_etaIntegralCore]
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      etaEulerSeries_constantCoeff 1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [coeff_etaEulerCoreAtScale, h]

/-- The integral numerator of the normalized level-six eta quotient. -/
noncomputable def levelSixRescaledEulerNumerator : PowerSeries ℤ :=
  etaEulerCoreAtScale 1 ^ 5 * etaEulerCoreAtScale 3

theorem levelSixRescaledEulerNumerator_constantCoeff :
    constantCoeff levelSixRescaledEulerNumerator = 1 := by
  simp [levelSixRescaledEulerNumerator, etaEulerCoreAtScale_constantCoeff]

/-- The integral denominator of the normalized level-six eta quotient. -/
noncomputable def levelSixRescaledEulerDenominator : PowerSeries ℤ :=
  etaEulerCoreAtScale 2 * etaEulerCoreAtScale 6 ^ 5

theorem levelSixRescaledEulerDenominator_constantCoeff :
    constantCoeff levelSixRescaledEulerDenominator = 1 := by
  simp [levelSixRescaledEulerDenominator, etaEulerCoreAtScale_constantCoeff]

/-- The integral formal series for `q t(τ)` obtained by inverting the
denominator with unit constant coefficient. -/
noncomputable def levelSixRescaledEulerUnit : PowerSeries ℤ :=
  levelSixRescaledEulerNumerator *
    levelSixRescaledEulerDenominator.invOfUnit 1

theorem levelSixRescaledEulerUnit_mul_denominator :
    levelSixRescaledEulerUnit * levelSixRescaledEulerDenominator =
      levelSixRescaledEulerNumerator := by
  unfold levelSixRescaledEulerUnit
  rw [mul_assoc, mul_comm (levelSixRescaledEulerDenominator.invOfUnit 1),
    PowerSeries.mul_invOfUnit _ _ levelSixRescaledEulerDenominator_constantCoeff,
    mul_one]

/-- The rescaled Euler unit satisfies the quotient equation in its core factors. -/
theorem levelSixRescaledEulerUnit_mul_coreFactors :
    levelSixRescaledEulerUnit * (etaEulerCoreAtScale 2 * etaEulerCoreAtScale 6 ^ 5) =
      etaEulerCoreAtScale 1 ^ 5 * etaEulerCoreAtScale 3 :=
  levelSixRescaledEulerUnit_mul_denominator

/-- The numerator's integral coefficient series sums to the analytic Euler
numerator everywhere in the open nome disc. -/
theorem hasSum_levelSixRescaledEulerNumerator {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun k => (levelSixRescaledEulerNumerator.coeff k : ℂ) * q ^ k)
      (etaEulerProduct q ^ 5 * etaEulerProduct (q ^ 3)) := by
  have h1 := hasSum_etaEulerCoreAtScale (by decide : 0 < 1) hq
  have h3 := hasSum_etaEulerCoreAtScale (by decide : 0 < 3) hq
  have hpow := QSeries.hasSum_coefficientTerm_pow
    (etaEulerCoreAtScale 1) q (etaEulerProduct (q ^ 1)) 5 h1
  simpa only [levelSixRescaledEulerNumerator, pow_one] using
    QSeries.hasSum_coefficientTerm_mul _ _ q _ _
      hpow.summable.norm h3.summable.norm hpow h3

/-- The denominator's integral coefficient series sums to the analytic Euler
denominator everywhere in the open nome disc. -/
theorem hasSum_levelSixRescaledEulerDenominator {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun k => (levelSixRescaledEulerDenominator.coeff k : ℂ) * q ^ k)
      (etaEulerProduct (q ^ 2) * etaEulerProduct (q ^ 6) ^ 5) := by
  have h2 := hasSum_etaEulerCoreAtScale (by decide : 0 < 2) hq
  have h6 := hasSum_etaEulerCoreAtScale (by decide : 0 < 6) hq
  have hpow := QSeries.hasSum_coefficientTerm_pow
    (etaEulerCoreAtScale 6) q (etaEulerProduct (q ^ 6)) 5 h6
  simpa only [levelSixRescaledEulerDenominator] using
    QSeries.hasSum_coefficientTerm_mul _ _ q _ _
      h2.summable.norm hpow.summable.norm h2 hpow

/-- The actual Taylor series at zero of the holomorphic level-six Euler unit. -/
noncomputable def levelSixEulerTaylorSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    (n.factorial : ℂ)⁻¹ * iteratedDeriv n levelSixEulerUnit 0

/-- The actual Euler unit equals its Taylor sum throughout the open nome disc. -/
theorem hasSum_levelSixEulerTaylorSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => levelSixEulerTaylorSeries.coeff n * q ^ n)
      (levelSixEulerUnit q) := by
  have hf : DifferentiableOn ℂ levelSixEulerUnit (Metric.ball 0 1) := by
    intro z hz
    exact (differentiableAt_levelSixEulerUnit (by simpa using hz)).differentiableWithinAt
  have h := Complex.hasSum_taylorSeries_on_ball hf (z := q) (by simpa using hq)
  simpa [levelSixEulerTaylorSeries, smul_eq_mul, mul_assoc, mul_comm,
    mul_left_comm] using h

/-- The integral rescaled Euler quotient maps to the actual analytic Taylor
series. In particular, every Taylor coefficient of `q t(τ)` is integral. -/
theorem levelSixRescaledEulerUnit_map_eq_taylorSeries :
    levelSixRescaledEulerUnit.map (Int.castRingHom ℂ) =
      levelSixEulerTaylorSeries := by
  let D := levelSixRescaledEulerDenominator.map (Int.castRingHom ℂ)
  let N := levelSixRescaledEulerNumerator.map (Int.castRingHom ℂ)
  have hformal : D * levelSixRescaledEulerUnit.map (Int.castRingHom ℂ) = N := by
    have h := congrArg (PowerSeries.map (Int.castRingHom ℂ))
      levelSixRescaledEulerUnit_mul_denominator
    simpa [D, N, mul_comm] using h
  have hanalytic : D * levelSixEulerTaylorSeries = N := by
    apply PowerSeries.ext
    have hc := QSeries.coefficients_eq_of_hasSum
      (c := fun n => (D * levelSixEulerTaylorSeries).coeff n)
      (d := fun n => N.coeff n)
      (f := fun q => etaEulerProduct q ^ 5 * etaEulerProduct (q ^ 3))
      (fun q hq => ?_) (fun q hq => ?_)
    · exact congrFun hc
    · have hD : HasSum (fun n => D.coeff n * q ^ n)
          (etaEulerProduct (q ^ 2) * etaEulerProduct (q ^ 6) ^ 5) := by
        simpa [D] using hasSum_levelSixRescaledEulerDenominator hq
      have hT := hasSum_levelSixEulerTaylorSeries hq
      have hpow (n : ℕ) (hn : 0 < n) : ‖q ^ n‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg q) hq hn.ne'
      have h2 : etaEulerProduct (q ^ 2) ≠ 0 :=
        etaEulerProduct_ne_zero (hpow 2 (by decide))
      have h6 : etaEulerProduct (q ^ 6) ≠ 0 :=
        etaEulerProduct_ne_zero (hpow 6 (by decide))
      have hden : etaEulerProduct (q ^ 2) * etaEulerProduct (q ^ 6) ^ 5 ≠ 0 :=
        mul_ne_zero h2 (pow_ne_zero _ h6)
      have heq :
          (etaEulerProduct (q ^ 2) * etaEulerProduct (q ^ 6) ^ 5) *
              levelSixEulerUnit q =
            etaEulerProduct q ^ 5 * etaEulerProduct (q ^ 3) := by
        rw [levelSixEulerUnit_eq]
        field_simp [h2, h6]
      simpa only [heq] using
        QSeries.hasSum_complexPowerSeries_mul D levelSixEulerTaylorSeries q _ _ hD hT
    · simpa [N] using hasSum_levelSixRescaledEulerNumerator hq
  have hDconst : constantCoeff D = 1 := by
    have hm (n : ℕ) :
        constantCoeff ((etaEulerCoreAtScale n).map (Int.castRingHom ℂ)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply,
        etaEulerCoreAtScale_constantCoeff]
      norm_num
    simp [D, levelSixRescaledEulerDenominator, hm]
  have hDne : D ≠ 0 := by
    intro he
    rw [he, map_zero] at hDconst
    norm_num at hDconst
  exact mul_left_cancel₀ hDne (hformal.trans hanalytic.symm)

/-- The Taylor coefficients of the normalized level-six eta quotient are
integers, with their explicit integral formal source. -/
theorem levelSixEulerTaylorSeries_coeff_integral (n : ℕ) :
    levelSixEulerTaylorSeries.coeff n =
      (levelSixRescaledEulerUnit.coeff n : ℂ) := by
  have h := congrArg (fun F : PowerSeries ℂ => F.coeff n)
    levelSixRescaledEulerUnit_map_eq_taylorSeries
  simpa using h.symm

/-- The integral coefficient series of the normalized level-six eta quotient
sums to its actual Euler unit throughout the open nome disc. -/
theorem hasSum_levelSixRescaledEulerUnit {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (levelSixRescaledEulerUnit.coeff n : ℂ) * q ^ n)
      (levelSixEulerUnit q) := by
  simpa only [levelSixEulerTaylorSeries_coeff_integral] using
    hasSum_levelSixEulerTaylorSeries hq

end SptClassification
