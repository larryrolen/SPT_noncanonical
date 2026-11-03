/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientCuspsCyclotomic
public import SptClassification.ModularForms.EtaQuotientCuspsThirdExpansion

/-!
# Cyclotomic coefficients at the cusp one-third

The cusp-one-third Euler unit is the reciprocal of the cusp-one-half unit.
Its Taylor coefficients therefore arise from the reciprocal of the same
universal `ℤ[X]` Euler series. This is a local cusp expansion, not integral
descent of the global coordinate. See [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

open PowerSeries

theorem cuspHalfPolynomialEulerUnit_constantCoeff :
    constantCoeff cuspHalfPolynomialEulerUnit = 1 := by
  have h := congrArg constantCoeff cuspHalfPolynomialEulerUnit_mul_denominator
  have hn : constantCoeff cuspHalfPolynomialNumerator = 1 := by
    simp [cuspHalfPolynomialNumerator_eq,
      etaEulerCoreAtPolynomialPhase_constantCoeff]
  simpa only [map_mul, cuspHalfPolynomialDenominator_constantCoeff,
    one_mul, hn] using h

theorem cuspHalfFormalEulerUnit_constantCoeff :
    constantCoeff cuspHalfFormalEulerUnit = 1 := by
  have h := congrArg (fun F : PowerSeries ℂ => F.coeff 0)
    cuspHalfPolynomialEulerUnit_map
  rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    cuspHalfPolynomialEulerUnit_constantCoeff, map_one] at h
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h.symm

/-- The universal polynomial-phase expansion at cusp one-third. -/
noncomputable def cuspThirdPolynomialEulerUnit : PowerSeries (Polynomial ℤ) :=
  cuspHalfPolynomialEulerUnit.invOfUnit 1

theorem cuspThirdPolynomialEulerUnit_eq :
    cuspThirdPolynomialEulerUnit = cuspHalfPolynomialEulerUnit.invOfUnit 1 := (rfl)

/-- The complex formal expansion at cusp one-third. -/
noncomputable def cuspThirdFormalEulerUnit : PowerSeries ℂ :=
  cuspHalfFormalEulerUnit.invOfUnit 1

theorem cuspThirdPolynomialEulerUnit_mul_half :
    cuspHalfPolynomialEulerUnit * cuspThirdPolynomialEulerUnit = 1 := by
  exact PowerSeries.mul_invOfUnit _ _ cuspHalfPolynomialEulerUnit_constantCoeff

theorem cuspThirdFormalEulerUnit_mul_half :
    cuspHalfFormalEulerUnit * cuspThirdFormalEulerUnit = 1 := by
  exact PowerSeries.mul_invOfUnit _ _ cuspHalfFormalEulerUnit_constantCoeff

/-- Specializing the universal third-cusp expansion gives the complex formal
Euler unit. -/
theorem cuspThirdPolynomialEulerUnit_map :
    cuspThirdPolynomialEulerUnit.map
      (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        (Function.Periodic.qParam 1 (-1 / 3 : ℂ))) =
      cuspThirdFormalEulerUnit := by
  have h := congrArg
    (PowerSeries.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
      (Function.Periodic.qParam 1 (-1 / 3 : ℂ))))
    cuspThirdPolynomialEulerUnit_mul_half
  rw [map_mul, cuspHalfPolynomialEulerUnit_map, map_one] at h
  have hne : cuspHalfFormalEulerUnit ≠ 0 := by
    intro he
    have hc := cuspHalfFormalEulerUnit_constantCoeff
    rw [he, map_zero] at hc
    norm_num at hc
  exact mul_left_cancel₀ hne
    (h.trans cuspThirdFormalEulerUnit_mul_half.symm)

/-- The Taylor series of the actual analytic cusp-one-third Euler unit. -/
noncomputable def cuspThirdEulerTaylorSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    (n.factorial : ℂ)⁻¹ * iteratedDeriv n cuspThirdEulerUnit 0

theorem hasSum_cuspThirdEulerTaylorSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => cuspThirdEulerTaylorSeries.coeff n * q ^ n)
      (cuspThirdEulerUnit q) := by
  have hf : DifferentiableOn ℂ cuspThirdEulerUnit (Metric.ball 0 1) := by
    intro z hz
    exact (differentiableAt_cuspThirdEulerUnit
      (by simpa using hz)).differentiableWithinAt
  have h := Complex.hasSum_taylorSeries_on_ball hf (z := q) (by simpa using hq)
  simpa [cuspThirdEulerTaylorSeries, smul_eq_mul, mul_assoc, mul_comm,
    mul_left_comm] using h

/-- The formal third-cusp Euler unit is the Taylor series of the actual
analytic reciprocal germ. -/
theorem cuspThirdFormalEulerUnit_eq_taylorSeries :
    cuspThirdFormalEulerUnit = cuspThirdEulerTaylorSeries := by
  have hprod : cuspHalfFormalEulerUnit * cuspThirdEulerTaylorSeries = 1 := by
    apply PowerSeries.ext
    have hc := QSeries.coefficients_eq_of_hasSum
      (c := fun n => (cuspHalfFormalEulerUnit * cuspThirdEulerTaylorSeries).coeff n)
      (d := fun n => (1 : PowerSeries ℂ).coeff n)
      (f := fun _ => (1 : ℂ))
      (fun q hq => ?_) (fun q hq => ?_)
    · exact congrFun hc
    · have hhalf := hasSum_cuspHalfFormalEulerUnit hq
      have hthird := hasSum_cuspThirdEulerTaylorSeries hq
      have heq : cuspHalfEulerUnit q * cuspThirdEulerUnit q = 1 := by
        rw [cuspThirdEulerUnit_eq]
        exact mul_inv_cancel₀ (cuspHalfEulerUnit_ne_zero hq)
      simpa only [heq] using
        QSeries.hasSum_complexPowerSeries_mul cuspHalfFormalEulerUnit
          cuspThirdEulerTaylorSeries q _ _ hhalf hthird
    · exact QSeries.hasSum_complexPowerSeries_one q
  have hne : cuspHalfFormalEulerUnit ≠ 0 := by
    intro he
    have hc := cuspHalfFormalEulerUnit_constantCoeff
    rw [he, map_zero] at hc
    norm_num at hc
  exact mul_left_cancel₀ hne
    (cuspThirdFormalEulerUnit_mul_half.trans hprod.symm)

/-- Every Taylor coefficient of the actual cusp-one-third Euler germ is an
integer polynomial evaluated at the cubic cusp phase. -/
theorem cuspThirdEulerTaylorCoeff_cyclotomic (n : ℕ) :
    cuspThirdEulerTaylorSeries.coeff n =
      Polynomial.eval₂ (Int.castRingHom ℂ)
        (Function.Periodic.qParam 1 (-1 / 3 : ℂ))
        (cuspThirdPolynomialEulerUnit.coeff n) := by
  have h := congrArg (fun F : PowerSeries ℂ => F.coeff n)
    (cuspThirdPolynomialEulerUnit_map.trans
      cuspThirdFormalEulerUnit_eq_taylorSeries)
  change cuspThirdEulerTaylorSeries.coeff n =
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
      (Function.Periodic.qParam 1 (-1 / 3 : ℂ)))
      (cuspThirdPolynomialEulerUnit.coeff n)
  simpa only [PowerSeries.coeff_map] using h.symm

end SptClassification
