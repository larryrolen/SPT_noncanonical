/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansionDerivative

/-!
# The eta coordinate has no critical point near infinity

The normalized derivative of the actual level-six eta quotient has constant
term `-1` at infinity. Its convergent integral expansion makes this derivative
holomorphic there, so it remains nonzero on a cusp neighborhood. This is a
local prerequisite for the coordinate argument in [rolen2026canonical],
Section 4; the assertion over the whole modular curve is separate.
-/

public section

namespace SptClassification

open PowerSeries

/-- The normalized derivative of the infinity-cusp eta coordinate is
holomorphic at the cusp. -/
theorem analyticAt_levelSixEtaCuspDerivative :
    AnalyticAt ℂ (fun q => q * deriv levelSixEulerUnit q - levelSixEulerUnit q) 0 := by
  have hsum : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n => (levelSixEtaDerivativeSeries.coeff n : ℂ) * q ^ n)
        (q * deriv levelSixEulerUnit q - levelSixEulerUnit q) :=
    fun _ hq => hasSum_levelSixEtaDerivativeSeries hq
  exact (QSeries.hasFPowerSeriesOnBall_of_hasSum hsum).hasFPowerSeriesAt.analyticAt

/-- The normalized cusp derivative takes the value `-1` at infinity. -/
theorem levelSixEtaCuspDerivative_zero :
    (0 : ℂ) * deriv levelSixEulerUnit 0 - levelSixEulerUnit 0 = -1 := by
  simp

/-- The actual eta quotient has nonzero normalized derivative sufficiently
close to the infinity cusp. -/
theorem eventually_levelSixEtaCuspDerivative_ne_zero :
    ∀ᶠ q : ℂ in nhds 0,
      q * deriv levelSixEulerUnit q - levelSixEulerUnit q ≠ 0 := by
  have hne : (0 : ℂ) * deriv levelSixEulerUnit 0 - levelSixEulerUnit 0 ≠ 0 := by
    rw [levelSixEtaCuspDerivative_zero]
    exact neg_ne_zero.mpr one_ne_zero
  exact analyticAt_levelSixEtaCuspDerivative.continuousAt.eventually_ne hne

/-- The punctured-disc expression for the eta coordinate has nonzero
ordinary derivative sufficiently close to infinity. -/
theorem eventually_deriv_levelSixInfinityCuspFunction_ne_zero :
    ∀ᶠ q : ℂ in nhds 0, q ≠ 0 →
      deriv (fun z : ℂ => levelSixEulerUnit z / z) q ≠ 0 := by
  have hball : ∀ᶠ q : ℂ in nhds 0, q ∈ Metric.ball 0 1 :=
    Metric.isOpen_ball.mem_nhds (by simp)
  filter_upwards [eventually_levelSixEtaCuspDerivative_ne_zero, hball]
    with q hne hq hq0
  have hq' : ‖q‖ < 1 := by simpa using hq
  have hU := (differentiableAt_levelSixEulerUnit hq').hasDerivAt
  have hdiv := hU.div (hasDerivAt_id q) hq0
  have hfun : (levelSixEulerUnit / id) =
      (fun z : ℂ => levelSixEulerUnit z / z) := by
    funext z
    rfl
  rw [hfun] at hdiv
  have hder : deriv (fun z : ℂ => levelSixEulerUnit z / z) q =
      (q * deriv levelSixEulerUnit q - levelSixEulerUnit q) / q ^ 2 := by
    simpa only [id_eq, mul_one, one_mul, mul_comm] using hdiv.deriv
  rw [hder]
  exact div_ne_zero hne (pow_ne_zero _ hq0)

end SptClassification
