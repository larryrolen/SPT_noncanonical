/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansionPhase

/-!
# Formal Euler factors at the cusp one-half

The width-three cusp one-half has eta factors with cubic phases. Their
formal series come from the integral eta core, and their coefficients sum
to the actual analytic Euler numerator and denominator. See
[rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

open PowerSeries

private theorem norm_qParam_one_real (c : ℝ) :
    ‖Function.Periodic.qParam 1 (c : ℂ)‖ = 1 := by
  unfold Function.Periodic.qParam
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

private theorem norm_cuspHalfPhase :
    ‖Function.Periodic.qParam 1 (-1 / 3 : ℂ)‖ = 1 := by
  have h : ((-1 / 3 : ℝ) : ℂ) = -1 / 3 := by norm_num
  rw [← h]
  exact norm_qParam_one_real _

private theorem norm_cuspThirdPhase :
    ‖Function.Periodic.qParam 1 (1 / 3 : ℂ)‖ = 1 := by
  have h : ((1 / 3 : ℝ) : ℂ) = 1 / 3 := by norm_num
  rw [← h]
  exact norm_qParam_one_real _

private theorem norm_cuspIntegralPhase :
    ‖Function.Periodic.qParam 1 (1 : ℂ)‖ = 1 := by
  have h : ((1 : ℝ) : ℂ) = 1 := by norm_num
  rw [← h]
  exact norm_qParam_one_real _

/-- The phase-rescaled numerator of the cusp-one-half Euler expression. -/
noncomputable def cuspHalfEulerNumeratorSeries : PowerSeries ℂ :=
  etaEulerCoreAtPhaseScale 3 1 ^ 5 *
    etaEulerCoreAtPhaseScale 1 (Function.Periodic.qParam 1 (-1 / 3))

theorem cuspHalfEulerNumeratorSeries_eq :
    cuspHalfEulerNumeratorSeries =
      etaEulerCoreAtPhaseScale 3 1 ^ 5 *
        etaEulerCoreAtPhaseScale 1 (Function.Periodic.qParam 1 (-1 / 3)) := (rfl)

/-- The phase-rescaled denominator of the cusp-one-half Euler expression. -/
noncomputable def cuspHalfEulerDenominatorSeries : PowerSeries ℂ :=
  etaEulerCoreAtPhaseScale 6 (Function.Periodic.qParam 1 1) *
    etaEulerCoreAtPhaseScale 2 (Function.Periodic.qParam 1 (1 / 3)) ^ 5

theorem cuspHalfEulerDenominatorSeries_eq :
    cuspHalfEulerDenominatorSeries =
      etaEulerCoreAtPhaseScale 6 (Function.Periodic.qParam 1 1) *
        etaEulerCoreAtPhaseScale 2 (Function.Periodic.qParam 1 (1 / 3)) ^ 5 := (rfl)

theorem cuspHalfEulerDenominatorSeries_constantCoeff :
    constantCoeff cuspHalfEulerDenominatorSeries = 1 := by
  simp [cuspHalfEulerDenominatorSeries, etaEulerCoreAtPhaseScale_constantCoeff]

/-- The formal cubic-phase expansion of the normalized quotient at cusp
one-half. Its denominator is a unit in complex power series. -/
noncomputable def cuspHalfFormalEulerUnit : PowerSeries ℂ :=
  cuspHalfEulerNumeratorSeries * cuspHalfEulerDenominatorSeries.invOfUnit 1

theorem cuspHalfFormalEulerUnit_mul_denominator :
    cuspHalfEulerDenominatorSeries * cuspHalfFormalEulerUnit =
      cuspHalfEulerNumeratorSeries := by
  unfold cuspHalfFormalEulerUnit
  rw [mul_comm cuspHalfEulerDenominatorSeries, mul_assoc,
    mul_comm (cuspHalfEulerDenominatorSeries.invOfUnit 1),
    PowerSeries.mul_invOfUnit _ _ cuspHalfEulerDenominatorSeries_constantCoeff,
    mul_one]

private theorem hasSum_complexPowerSeries_pow (F : PowerSeries ℂ)
    (q a : ℂ) (k : ℕ)
    (hF : HasSum (fun n => F.coeff n * q ^ n) a) :
    HasSum (fun n => (F ^ k).coeff n * q ^ n) (a ^ k) := by
  induction k with
  | zero =>
      simpa using QSeries.hasSum_complexPowerSeries_one q
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact QSeries.hasSum_complexPowerSeries_mul _ _ _ _ _ ih hF

/-- The formal numerator sums to the numerator of the actual cusp germ. -/
theorem hasSum_cuspHalfEulerNumeratorSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun k => cuspHalfEulerNumeratorSeries.coeff k * q ^ k)
      (etaEulerProduct (q ^ 3) ^ 5 *
        etaEulerProduct (q * Function.Periodic.qParam 1 (-1 / 3))) := by
  have h3 : HasSum
      (fun k => (etaEulerCoreAtPhaseScale 3 1).coeff k * q ^ k)
      (etaEulerProduct (q ^ 3)) := by
    simpa using hasSum_etaEulerCoreAtPhaseScale (by decide : 0 < 3)
      (by simp : ‖(1 : ℂ)‖ = 1) hq
  have h1 : HasSum
      (fun k => (etaEulerCoreAtPhaseScale 1
        (Function.Periodic.qParam 1 (-1 / 3))).coeff k * q ^ k)
      (etaEulerProduct (q * Function.Periodic.qParam 1 (-1 / 3))) := by
    simpa using hasSum_etaEulerCoreAtPhaseScale (by decide : 0 < 1)
      norm_cuspHalfPhase hq
  exact QSeries.hasSum_complexPowerSeries_mul _ _ _ _ _
    (hasSum_complexPowerSeries_pow _ _ _ 5 h3) h1

/-- The formal denominator sums to the denominator of the actual cusp germ. -/
theorem hasSum_cuspHalfEulerDenominatorSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun k => cuspHalfEulerDenominatorSeries.coeff k * q ^ k)
      (etaEulerProduct (q ^ 6 * Function.Periodic.qParam 1 1) *
        etaEulerProduct (q ^ 2 * Function.Periodic.qParam 1 (1 / 3)) ^ 5) := by
  have h6 := hasSum_etaEulerCoreAtPhaseScale (by decide : 0 < 6)
    norm_cuspIntegralPhase hq
  have h2 := hasSum_etaEulerCoreAtPhaseScale (by decide : 0 < 2)
    norm_cuspThirdPhase hq
  exact QSeries.hasSum_complexPowerSeries_mul _ _ _ _ _ h6
    (hasSum_complexPowerSeries_pow _ _ _ 5 h2)

/-- The Taylor series of the actual analytic cusp-one-half Euler unit. -/
noncomputable def cuspHalfEulerTaylorSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    (n.factorial : ℂ)⁻¹ * iteratedDeriv n cuspHalfEulerUnit 0

theorem hasSum_cuspHalfEulerTaylorSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => cuspHalfEulerTaylorSeries.coeff n * q ^ n)
      (cuspHalfEulerUnit q) := by
  have hf : DifferentiableOn ℂ cuspHalfEulerUnit (Metric.ball 0 1) := by
    intro z hz
    exact (differentiableAt_cuspHalfEulerUnit
      (by simpa using hz)).differentiableWithinAt
  have h := Complex.hasSum_taylorSeries_on_ball hf (z := q) (by simpa using hq)
  simpa [cuspHalfEulerTaylorSeries, smul_eq_mul, mul_assoc, mul_comm,
    mul_left_comm] using h

/-- The formal cubic-phase quotient is precisely the Taylor series of the
actual cusp-one-half Euler germ. -/
theorem cuspHalfFormalEulerUnit_eq_taylorSeries :
    cuspHalfFormalEulerUnit = cuspHalfEulerTaylorSeries := by
  let D := cuspHalfEulerDenominatorSeries
  let N := cuspHalfEulerNumeratorSeries
  have hformal : D * cuspHalfFormalEulerUnit = N :=
    cuspHalfFormalEulerUnit_mul_denominator
  have hanalytic : D * cuspHalfEulerTaylorSeries = N := by
    apply PowerSeries.ext
    have hc := QSeries.coefficients_eq_of_hasSum
      (c := fun n => (D * cuspHalfEulerTaylorSeries).coeff n)
      (d := fun n => N.coeff n)
      (f := fun q => etaEulerProduct (q ^ 3) ^ 5 *
        etaEulerProduct (q * Function.Periodic.qParam 1 (-1 / 3)))
      (fun q hq => ?_) (fun q hq => ?_)
    · exact congrFun hc
    · have hD := hasSum_cuspHalfEulerDenominatorSeries hq
      have hT := hasSum_cuspHalfEulerTaylorSeries hq
      have h6arg : ‖q ^ 6 * Function.Periodic.qParam 1 1‖ < 1 := by
        rw [norm_mul, norm_pow, norm_cuspIntegralPhase, mul_one]
        exact pow_lt_one₀ (norm_nonneg q) hq (by decide)
      have h2arg : ‖q ^ 2 * Function.Periodic.qParam 1 (1 / 3)‖ < 1 := by
        rw [norm_mul, norm_pow, norm_cuspThirdPhase, mul_one]
        exact pow_lt_one₀ (norm_nonneg q) hq (by decide)
      have hden : etaEulerProduct (q ^ 6 * Function.Periodic.qParam 1 1) *
          etaEulerProduct (q ^ 2 * Function.Periodic.qParam 1 (1 / 3)) ^ 5 ≠ 0 :=
        mul_ne_zero (etaEulerProduct_ne_zero h6arg)
          (pow_ne_zero _ (etaEulerProduct_ne_zero h2arg))
      have heq :
          (etaEulerProduct (q ^ 6 * Function.Periodic.qParam 1 1) *
            etaEulerProduct (q ^ 2 * Function.Periodic.qParam 1 (1 / 3)) ^ 5) *
            cuspHalfEulerUnit q =
          etaEulerProduct (q ^ 3) ^ 5 *
            etaEulerProduct (q * Function.Periodic.qParam 1 (-1 / 3)) := by
        rw [cuspHalfEulerUnit_eq]
        exact mul_div_cancel₀ _ hden
      simpa only [heq] using
        QSeries.hasSum_complexPowerSeries_mul D cuspHalfEulerTaylorSeries q _ _ hD hT
    · simpa [N] using hasSum_cuspHalfEulerNumeratorSeries hq
  have hDne : D ≠ 0 := by
    intro he
    have h := cuspHalfEulerDenominatorSeries_constantCoeff
    change constantCoeff D = 1 at h
    rw [he, map_zero] at h
    norm_num at h
  exact mul_left_cancel₀ hDne (hformal.trans hanalytic.symm)

/-- The cubic-phase formal coefficients sum to the analytic cusp germ on
the full open nome disc. -/
theorem hasSum_cuspHalfFormalEulerUnit {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => cuspHalfFormalEulerUnit.coeff n * q ^ n)
      (cuspHalfEulerUnit q) := by
  rw [cuspHalfFormalEulerUnit_eq_taylorSeries]
  exact hasSum_cuspHalfEulerTaylorSeries hq

end SptClassification
