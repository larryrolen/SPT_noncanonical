/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMAnalyticCuspClearing
public import SptClassification.ModularForms.EtaQuotientExpansion
public import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# CM cusp clearing for the actual eta coordinate

The local homogeneous-polynomial cancellation is specialized to the actual
eta quotient and modular discriminant in [rolenManuscript, Section 4].
The resulting cusp factor is analytic with constant term one.
-/

public section

namespace SptClassification

/-- The Euler product is analytic throughout its open nome disc. -/
theorem analyticAt_etaEulerProduct {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticAt ℂ etaEulerProduct q :=
  differentiableOn_etaEulerProduct.analyticAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hq))

/-- The normalized actual eta coordinate is analytic on the open nome disc. -/
theorem analyticAt_levelSixEulerUnit {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticAt ℂ levelSixEulerUnit q := by
  have h : DifferentiableOn ℂ levelSixEulerUnit (Metric.ball 0 1) := by
    intro z hz
    exact (differentiableAt_levelSixEulerUnit (by simpa using hz)).differentiableWithinAt
  exact h.analyticAt (Metric.isOpen_ball.mem_nhds (by simpa using hq))

/-- The discriminant is the nome times the twenty-fourth power of the
actual Euler unit, with no unspecified normalization constant. -/
theorem discriminant_eq_etaEulerProduct (z : UpperHalfPlane) :
    ModularForm.discriminant z = Function.Periodic.qParam 1 z *
      etaEulerProduct (Function.Periodic.qParam 1 z) ^ 24 := by
  rw [ModularForm.discriminant]
  have heta := eta_nat_mul_eq_euler 1 (z : ℂ)
  simp only [Nat.cast_one, one_mul, pow_one] at heta
  rw [heta, mul_pow]
  congr 1
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- The actual CM clearing factor, expressed in the infinity nome chart. -/
noncomputable def cmActualCuspClearingFactor (D : ℤ) [Fact (D < 0)] : ℂ → ℂ :=
  cmAnalyticCuspClearingFactor D levelSixEulerUnit (fun q => etaEulerProduct q ^ 24)

/-- The actual normalized CM clearing factor is analytic at infinity. -/
theorem analyticAt_cmActualCuspClearingFactor (D : ℤ) [Fact (D < 0)] :
    AnalyticAt ℂ (cmActualCuspClearingFactor D) 0 :=
  analyticAt_cmAnalyticCuspClearingFactor D
    (analyticAt_levelSixEulerUnit (by simp)) ((analyticAt_etaEulerProduct (by simp)).pow 24)

/-- The actual clearing factor is analytic throughout the open nome disc. -/
theorem analyticAt_cmActualCuspClearingFactor_of_norm_lt_one
    (D : ℤ) [Fact (D < 0)] {q : ℂ} (hq : ‖q‖ < 1) :
    AnalyticAt ℂ (cmActualCuspClearingFactor D) q :=
  analyticAt_cmAnalyticCuspClearingFactor D
    (analyticAt_levelSixEulerUnit hq) ((analyticAt_etaEulerProduct hq).pow 24)

/-- The actual CM clearing factor preserves constant terms at infinity. -/
@[simp] theorem cmActualCuspClearingFactor_zero (D : ℤ) [Fact (D < 0)] :
    cmActualCuspClearingFactor D 0 = 1 :=
  cmAnalyticCuspClearingFactor_zero D levelSixEulerUnit_zero (by simp)

/-- Evaluation on the upper half-plane agrees with the actual paired CM
polynomial factor and the actual modular discriminant. -/
theorem cmActualCuspClearingFactor_qParam (D : ℤ) [Fact (D < 0)]
    (hD : D % 24 = 1) (z : UpperHalfPlane) :
    cmActualCuspClearingFactor D (Function.Periodic.qParam 1 z) =
      ((cmClassPolynomialA D).eval (levelSixEtaQuotient z) *
        (cmClassPolynomialB D).eval (levelSixEtaQuotient z)) ^ 2 *
          ModularForm.discriminant z ^ (8 * formClassNumber D) := by
  rw [cmActualCuspClearingFactor, cmAnalyticCuspClearingFactor_eq D hD]
  · rw [← levelSixEtaQuotient_eq_unit_div_qParam,
      ← discriminant_eq_etaEulerProduct]
  · exact Complex.exp_ne_zero _

/-- Multiplication by the actual pole-clearing factor gives an analytic cusp
extension and preserves the constant term of every analytic lift. -/
theorem cm_actual_cusp_clearing_extension (D : ℤ) [Fact (D < 0)]
    (hD : D % 24 = 1) {J : ℂ → ℂ} (hJ : AnalyticAt ℂ J 0) :
    ∃ F : ℂ → ℂ, AnalyticAt ℂ F 0 ∧ F 0 = J 0 ∧
      ∀ z : UpperHalfPlane, F (Function.Periodic.qParam 1 z) =
        ((cmClassPolynomialA D).eval (levelSixEtaQuotient z) *
          (cmClassPolynomialB D).eval (levelSixEtaQuotient z)) ^ 2 *
            ModularForm.discriminant z ^ (8 * formClassNumber D) *
              J (Function.Periodic.qParam 1 z) := by
  refine ⟨fun q => cmActualCuspClearingFactor D q * J q,
    (analyticAt_cmActualCuspClearingFactor D).mul hJ, by simp, ?_⟩
  intro z
  dsimp only
  rw [cmActualCuspClearingFactor_qParam D hD]

end SptClassification
