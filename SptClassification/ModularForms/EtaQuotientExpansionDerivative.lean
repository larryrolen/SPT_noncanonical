/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansionTaylor
public import SptClassification.QSeries.ConvergentDerivatives
public import SptClassification.QSeries.EulerDerivative

/-!
# The derivative of the level-six eta coordinate at infinity

Writing the eta coordinate as `t = U(q)/q`, its Euler derivative has the
integral expansion `q Θt = q U'(q) - U(q)`. The constant coefficient is `-1`.
This is the normalized infinity-cusp derivative needed in the coordinate
argument of [rolen2026canonical], Section 4. Global nonvanishing on the
integral modular curve is a separate geometric statement.
-/

public section

namespace SptClassification

open PowerSeries

/-- The integral coefficient series for `q Θt` at the infinity cusp. -/
noncomputable def levelSixEtaDerivativeSeries : PowerSeries ℤ :=
  QSeries.eulerDerivative levelSixRescaledEulerUnit - levelSixRescaledEulerUnit

/-- The coefficient of `qⁿ` in `q Θt` is `(n-1)` times the coefficient of
`qⁿ` in the Euler unit. -/
theorem levelSixEtaDerivativeSeries_coeff (n : ℕ) :
    levelSixEtaDerivativeSeries.coeff n =
      ((n : ℤ) - 1) * levelSixRescaledEulerUnit.coeff n := by
  simp only [levelSixEtaDerivativeSeries, map_sub, QSeries.coeff_eulerDerivative]
  ring

/-- The normalized cusp derivative begins with `-1`. -/
theorem levelSixEtaDerivativeSeries_constantCoeff :
    constantCoeff levelSixEtaDerivativeSeries = -1 := by
  have hU : constantCoeff levelSixRescaledEulerUnit = 1 := by
    simpa only [map_mul, levelSixRescaledEulerDenominator_constantCoeff,
      levelSixRescaledEulerNumerator_constantCoeff, mul_one] using
      congrArg constantCoeff levelSixRescaledEulerUnit_mul_denominator
  rw [← coeff_zero_eq_constantCoeff_apply, levelSixEtaDerivativeSeries_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hU]
  norm_num

/-- The integral derivative series sums to `q U'(q)-U(q)` on the open disc. -/
theorem hasSum_levelSixEtaDerivativeSeries {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (levelSixEtaDerivativeSeries.coeff n : ℂ) * q ^ n)
      (q * deriv levelSixEulerUnit q - levelSixEulerUnit q) := by
  have hc : ∀ z : ℂ, ‖z‖ < 1 →
      HasSum (fun n => (levelSixRescaledEulerUnit.coeff n : ℂ) * z ^ n)
        (levelSixEulerUnit z) :=
    fun _ hz => hasSum_levelSixRescaledEulerUnit hz
  have hd := QSeries.hasSum_eulerDerivative_of_hasSum hc hq
  have h := hd.sub (hc q hq)
  convert h using 1
  ext n
  rw [levelSixEtaDerivativeSeries_coeff]
  push_cast
  ring

/-- On the punctured disc, the integral derivative series is `q² d(U/q)/dq`. -/
theorem hasSum_levelSixEtaDerivativeSeries_cusp {q : ℂ}
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasSum (fun n => (levelSixEtaDerivativeSeries.coeff n : ℂ) * q ^ n)
      (q ^ 2 * deriv (fun z : ℂ => levelSixEulerUnit z / z) q) := by
  have hU := (differentiableAt_levelSixEulerUnit hq).hasDerivAt
  have hdiv := hU.div (hasDerivAt_id q) hq0
  have hfun : (levelSixEulerUnit / id) =
      (fun z : ℂ => levelSixEulerUnit z / z) := by
    funext z
    rfl
  have hder : deriv (fun z : ℂ => levelSixEulerUnit z / z) q =
      (q * deriv levelSixEulerUnit q - levelSixEulerUnit q) / q ^ 2 := by
    rw [hfun] at hdiv
    simpa only [id_eq, mul_one, one_mul, mul_comm] using hdiv.deriv
  rw [hder]
  convert hasSum_levelSixEtaDerivativeSeries hq using 1
  field_simp [hq0]

/-- The punctured-disc cusp function is the actual level-six eta quotient
after applying the ordinary nome to an upper-half-plane point. -/
theorem levelSixEtaQuotient_eq_infinityCuspFunction (z : UpperHalfPlane) :
    levelSixEtaQuotient (z : ℂ) =
      levelSixEulerUnit (Function.Periodic.qParam 1 z) /
        Function.Periodic.qParam 1 z := by
  have hq : Function.Periodic.qParam 1 z ≠ 0 := by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _
  apply (eq_div_iff hq).2
  simpa only [mul_comm] using qParam_mul_levelSixEtaQuotient z

end SptClassification
