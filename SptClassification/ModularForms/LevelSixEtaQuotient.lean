/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum

/-!
# The level-six eta quotient

We use the explicit function
`eta(z)^5 * eta(3z) / (eta(2z) * eta(6z)^5)` from [rolen2026canonical],
equation (4.1). The assertions here concern its actual analytic formula on the
upper half-plane. Its identification with an integral modular-curve coordinate
requires additional geometric results.
-/

@[expose] public section

namespace SptClassification

/-- Positive real rescaling preserves nonvanishing of the Dedekind eta function. -/
theorem eta_pos_mul_ne_zero (r : ℝ) (hr : 0 < r) (z : UpperHalfPlane) :
    ModularForm.eta ((r : ℂ) * (z : ℂ)) ≠ 0 := by
  apply ModularForm.eta_ne_zero
  simpa using mul_pos hr z.im_pos

/-- Eta remains holomorphic after a positive real rescaling. -/
theorem differentiableAt_eta_pos_mul (r : ℝ) (hr : 0 < r) (z : UpperHalfPlane) :
    DifferentiableAt ℂ (fun w : ℂ => ModularForm.eta ((r : ℂ) * w)) (z : ℂ) := by
  have hz : 0 < ((r : ℂ) * (z : ℂ)).im := by simpa using mul_pos hr z.im_pos
  have hf := ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hz
  have hg : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ) * w) (z : ℂ) := by fun_prop
  exact hf.comp (z : ℂ) hg

/-- The explicit level-six eta quotient used to evaluate CM points. -/
noncomputable def levelSixEtaQuotient (z : ℂ) : ℂ :=
  ModularForm.eta z ^ 5 * ModularForm.eta (3 * z) /
    (ModularForm.eta (2 * z) * ModularForm.eta (6 * z) ^ 5)

/-- The analytic formula for the level-six eta quotient. -/
theorem levelSixEtaQuotient_eq (z : ℂ) :
    levelSixEtaQuotient z =
      ModularForm.eta z ^ 5 * ModularForm.eta (3 * z) /
        (ModularForm.eta (2 * z) * ModularForm.eta (6 * z) ^ 5) :=
  (rfl)

/-- The eta quotient is nonzero at every point of the upper half-plane. -/
theorem levelSixEtaQuotient_ne_zero (z : UpperHalfPlane) :
    levelSixEtaQuotient (z : ℂ) ≠ 0 := by
  have h1 := ModularForm.eta_ne_zero z.im_pos
  have h2 : ModularForm.eta (2 * (z : ℂ)) ≠ 0 := by
    simpa using eta_pos_mul_ne_zero 2 (by norm_num) z
  have h3 : ModularForm.eta (3 * (z : ℂ)) ≠ 0 := by
    simpa using eta_pos_mul_ne_zero 3 (by norm_num) z
  have h6 : ModularForm.eta (6 * (z : ℂ)) ≠ 0 := by
    simpa using eta_pos_mul_ne_zero 6 (by norm_num) z
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 5 h1) h3)
    (mul_ne_zero h2 (pow_ne_zero 5 h6))

/-- The analytic eta quotient is holomorphic on the upper half-plane. -/
theorem differentiableAt_levelSixEtaQuotient (z : UpperHalfPlane) :
    DifferentiableAt ℂ levelSixEtaQuotient (z : ℂ) := by
  have h1 := ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet z.im_pos
  have h2 : DifferentiableAt ℂ (fun w : ℂ => ModularForm.eta (2 * w)) (z : ℂ) := by
    simpa using differentiableAt_eta_pos_mul 2 (by norm_num) z
  have h3 : DifferentiableAt ℂ (fun w : ℂ => ModularForm.eta (3 * w)) (z : ℂ) := by
    simpa using differentiableAt_eta_pos_mul 3 (by norm_num) z
  have h6 : DifferentiableAt ℂ (fun w : ℂ => ModularForm.eta (6 * w)) (z : ℂ) := by
    simpa using differentiableAt_eta_pos_mul 6 (by norm_num) z
  have n2 : ModularForm.eta (2 * (z : ℂ)) ≠ 0 := by
    simpa using eta_pos_mul_ne_zero 2 (by norm_num) z
  have n6 : ModularForm.eta (6 * (z : ℂ)) ≠ 0 := by
    simpa using eta_pos_mul_ne_zero 6 (by norm_num) z
  exact ((h1.pow 5).mul h3).div (h2.mul (h6.pow 5))
    (mul_ne_zero n2 (pow_ne_zero 5 n6))

/-- Continuity of the upper-half-plane eta quotient. -/
theorem continuous_levelSixEtaQuotient :
    Continuous (fun z : UpperHalfPlane => levelSixEtaQuotient (z : ℂ)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (differentiableAt_levelSixEtaQuotient z).continuousAt.comp
    UpperHalfPlane.continuous_coe.continuousAt

end SptClassification
