/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientCuspsPhaseExpansion

/-!
# Cyclotomic coefficients at the width-three cusp

The phase in the cusp-one-half expansion is a cubic root of unity. We first
construct its Euler quotient over `ℤ[X]`, then specialize `X` to that phase.
Thus every analytic Taylor coefficient of the local cusp germ is the value
of an integer polynomial at a cubic root of unity. This is local arithmetic
information; the integral coordinate on the modular curve requires a
separate descent argument. See [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

open PowerSeries

/-- The eta core rescaled in the nome and twisted by a polynomial phase. -/
noncomputable def etaEulerCoreAtPolynomialPhase
    (n : ℕ) (P : Polynomial ℤ) : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun j =>
    if n ∣ j then Polynomial.C (QSeries.etaIntegralCore.coeff (j / n)) *
      P ^ (j / n) else 0

theorem coeff_etaEulerCoreAtPolynomialPhase (n j : ℕ) (P : Polynomial ℤ) :
    (etaEulerCoreAtPolynomialPhase n P).coeff j =
      if n ∣ j then Polynomial.C (QSeries.etaIntegralCore.coeff (j / n)) *
        P ^ (j / n) else 0 := by
  simp [etaEulerCoreAtPolynomialPhase]

theorem etaEulerCoreAtPolynomialPhase_constantCoeff
    (n : ℕ) (P : Polynomial ℤ) :
    constantCoeff (etaEulerCoreAtPolynomialPhase n P) = 1 := by
  have h : QSeries.etaIntegralCore.coeff 0 = 1 := by
    rw [← etaEulerSeries_one_eq_etaIntegralCore]
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      etaEulerSeries_constantCoeff 1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [etaEulerCoreAtPolynomialPhase, h]

/-- Evaluating the polynomial phase commutes with forming its formal eta
core. -/
theorem etaEulerCoreAtPolynomialPhase_map (n : ℕ) (P : Polynomial ℤ)
    (ω : ℂ) :
    (etaEulerCoreAtPolynomialPhase n P).map
      (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) =
    etaEulerCoreAtPhaseScale n
      (Polynomial.eval₂ (Int.castRingHom ℂ) ω P) := by
  apply PowerSeries.ext
  intro j
  rw [PowerSeries.coeff_map]
  by_cases hj : n ∣ j
  · simp only [coeff_etaEulerCoreAtPolynomialPhase,
      coeff_etaEulerCoreAtPhaseScale, hj, ↓reduceIte]
    rw [map_mul, map_pow]
    change Polynomial.eval₂ (Int.castRingHom ℂ) ω
      (Polynomial.C (QSeries.etaIntegralCore.coeff (j / n))) *
      Polynomial.eval₂ (Int.castRingHom ℂ) ω P ^ (j / n) = _
    rw [Polynomial.eval₂_C]
    rfl
  · simp [coeff_etaEulerCoreAtPolynomialPhase,
      coeff_etaEulerCoreAtPhaseScale, hj]

/-- The universal polynomial-phase numerator at cusp one-half. -/
noncomputable def cuspHalfPolynomialNumerator : PowerSeries (Polynomial ℤ) :=
  etaEulerCoreAtPolynomialPhase 3 1 ^ 5 *
    etaEulerCoreAtPolynomialPhase 1 Polynomial.X

theorem cuspHalfPolynomialNumerator_eq :
    cuspHalfPolynomialNumerator =
      etaEulerCoreAtPolynomialPhase 3 1 ^ 5 *
        etaEulerCoreAtPolynomialPhase 1 Polynomial.X := (rfl)

/-- The universal polynomial-phase denominator at cusp one-half. -/
noncomputable def cuspHalfPolynomialDenominator : PowerSeries (Polynomial ℤ) :=
  etaEulerCoreAtPolynomialPhase 6 1 *
    etaEulerCoreAtPolynomialPhase 2 (Polynomial.X ^ 2) ^ 5

theorem cuspHalfPolynomialDenominator_eq :
    cuspHalfPolynomialDenominator =
      etaEulerCoreAtPolynomialPhase 6 1 *
        etaEulerCoreAtPolynomialPhase 2 (Polynomial.X ^ 2) ^ 5 := (rfl)

theorem cuspHalfPolynomialDenominator_constantCoeff :
    constantCoeff cuspHalfPolynomialDenominator = 1 := by
  simp [cuspHalfPolynomialDenominator,
    etaEulerCoreAtPolynomialPhase_constantCoeff]

/-- The universal cusp-one-half Euler quotient has coefficients in `ℤ[X]`.
Its specialized coefficients therefore lie in the cubic cyclotomic order. -/
noncomputable def cuspHalfPolynomialEulerUnit :
    PowerSeries (Polynomial ℤ) :=
  cuspHalfPolynomialNumerator *
    cuspHalfPolynomialDenominator.invOfUnit 1

theorem cuspHalfPolynomialEulerUnit_mul_denominator :
    cuspHalfPolynomialDenominator * cuspHalfPolynomialEulerUnit =
      cuspHalfPolynomialNumerator := by
  unfold cuspHalfPolynomialEulerUnit
  rw [mul_comm cuspHalfPolynomialDenominator, mul_assoc,
    mul_comm (cuspHalfPolynomialDenominator.invOfUnit 1),
    PowerSeries.mul_invOfUnit _ _ cuspHalfPolynomialDenominator_constantCoeff,
    mul_one]

private theorem cuspHalfPhase_sq :
    Function.Periodic.qParam 1 (-1 / 3 : ℂ) ^ 2 =
      Function.Periodic.qParam 1 (1 / 3 : ℂ) := by
  unfold Function.Periodic.qParam
  have hone : ((1 : ℝ) : ℂ) = 1 := by norm_num
  rw [hone, div_one]
  rw [pow_two, ← Complex.exp_add]
  have h :
      (2 * (Real.pi : ℂ) * Complex.I * (-1 / 3 : ℂ)) +
        (2 * (Real.pi : ℂ) * Complex.I * (-1 / 3 : ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I * (1 / 3 : ℂ)) -
        2 * (Real.pi : ℂ) * Complex.I := by ring
  rw [h, Complex.exp_sub, Complex.exp_two_pi_mul_I]
  simp

private theorem cuspIntegralPhase_eq_one :
    Function.Periodic.qParam 1 (1 : ℂ) = 1 := by
  unfold Function.Periodic.qParam
  have hone : ((1 : ℝ) : ℂ) = 1 := by norm_num
  rw [hone, div_one, mul_one]
  exact Complex.exp_two_pi_mul_I

theorem cuspHalfPolynomialNumerator_map :
    cuspHalfPolynomialNumerator.map
      (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        (Function.Periodic.qParam 1 (-1 / 3 : ℂ))) =
      cuspHalfEulerNumeratorSeries := by
  rw [cuspHalfPolynomialNumerator_eq, cuspHalfEulerNumeratorSeries_eq]
  rw [map_mul, map_pow, etaEulerCoreAtPolynomialPhase_map,
    etaEulerCoreAtPolynomialPhase_map]
  simp

theorem cuspHalfPolynomialDenominator_map :
    cuspHalfPolynomialDenominator.map
      (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        (Function.Periodic.qParam 1 (-1 / 3 : ℂ))) =
      cuspHalfEulerDenominatorSeries := by
  rw [cuspHalfPolynomialDenominator_eq, cuspHalfEulerDenominatorSeries_eq]
  rw [map_mul, map_pow, etaEulerCoreAtPolynomialPhase_map,
    etaEulerCoreAtPolynomialPhase_map]
  simp [cuspHalfPhase_sq, cuspIntegralPhase_eq_one]

/-- The universal integral-polynomial Euler quotient specializes to the
formal cubic-phase expansion of the actual cusp germ. -/
theorem cuspHalfPolynomialEulerUnit_map :
    cuspHalfPolynomialEulerUnit.map
      (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        (Function.Periodic.qParam 1 (-1 / 3 : ℂ))) =
      cuspHalfFormalEulerUnit := by
  have h := congrArg
    (PowerSeries.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
      (Function.Periodic.qParam 1 (-1 / 3 : ℂ))))
    cuspHalfPolynomialEulerUnit_mul_denominator
  rw [map_mul, cuspHalfPolynomialDenominator_map,
    cuspHalfPolynomialNumerator_map] at h
  have hne : cuspHalfEulerDenominatorSeries ≠ 0 := by
    intro he
    have hc := cuspHalfEulerDenominatorSeries_constantCoeff
    rw [he, map_zero] at hc
    norm_num at hc
  exact mul_left_cancel₀ hne
    (h.trans cuspHalfFormalEulerUnit_mul_denominator.symm)

/-- Every Taylor coefficient of the analytic cusp-one-half Euler germ is an
integer polynomial evaluated at its cubic phase. -/
theorem cuspHalfEulerTaylorCoeff_cyclotomic (n : ℕ) :
    cuspHalfEulerTaylorSeries.coeff n =
      Polynomial.eval₂ (Int.castRingHom ℂ)
        (Function.Periodic.qParam 1 (-1 / 3 : ℂ))
        (cuspHalfPolynomialEulerUnit.coeff n) := by
  have h := congrArg (fun F : PowerSeries ℂ => F.coeff n)
    (cuspHalfPolynomialEulerUnit_map.trans
      cuspHalfFormalEulerUnit_eq_taylorSeries)
  change cuspHalfEulerTaylorSeries.coeff n =
    (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
      (Function.Periodic.qParam 1 (-1 / 3 : ℂ)))
      (cuspHalfPolynomialEulerUnit.coeff n)
  simpa only [PowerSeries.coeff_map] using h.symm

end SptClassification
