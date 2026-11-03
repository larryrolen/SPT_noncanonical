/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMShimuraFiniteCuspComparison
public import SptClassification.ModularForms.CMGlobalCuspClearing

/-!
# Finite cusp bounds for the actual principal CM lift

The same independently constructed lift has a holomorphic nome germ in each
finite chart. The explicit product and classical slash comparison transfer
its bound to the removable CM extension. No new global lift is chosen.
[rolenManuscript, Section 4, proof of prop:obstruction]
-/

public section

namespace SptClassification

open Filter UpperHalfPlane OnePoint
open scoped Topology MatrixGroups

/-- The actual cleared principal lift is bounded at each of the three finite
cusps. The slash is normalized with the positive chart determinant. -/
theorem principalCMShimuraLift_finite_cusp_bound (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hmod : d % 24 = 23)
    (F : ℂ → ℂ) (Y : ℝ)
    (hanalytic : AnalyticOnNhd ℂ
      (cmPoleClearedFunction (-(d : ℤ)) F) {w | 0 < w.im})
    (hgerm : ∀ z : UpperHalfPlane,
      (fun w => cmPoleFactor (-(d : ℤ)) w ^ 2 * F w) =ᶠ[𝓝[≠] (z : ℂ)]
        cmPoleClearedFunction (-(d : ℤ)) F)
    (hsum : ∀ z : UpperHalfPlane, Y < z.im →
      HasSum (fun n : ℕ =>
        ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
          Function.Periodic.qParam 1 z ^ n) (F z))
    (hslash : ∀ (c : FiniteLevelSixCusp) (z : UpperHalfPlane),
      c.weightFourSlash F z = (c.atkinSign : ℂ) * F (c.shiftedPoint z))
    (c : FiniteLevelSixCusp) :
    (c.chartGL • (∞ : OnePoint ℝ)).IsBoundedAt
      (fun z : UpperHalfPlane =>
        ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
          cmPoleClearedFunction (-(d : ℤ)) F z)
      ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ) := by
  let H : ℝ := max Y 0 + 1
  have hH : 0 < H := by dsimp [H]; positivity
  have hY : Y < H := by dsimp [H]; linarith [le_max_left Y 0]
  let z₀ : UpperHalfPlane := ⟨⟨0, H⟩, hH⟩
  obtain ⟨Jc, hJc, _, hJq⟩ :=
    principalCMShimuraLift_finite_cusp_germ d hmod F Y hsum hslash c z₀ hY
  have hq : 0 < ‖Function.Periodic.qParam 1 z₀‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hanalyticG : AnalyticAt ℂ
      (c.clearedShimuraGerm (-(d : ℤ)) Jc) 0 :=
    c.analyticAt_clearedShimuraGerm (-(d : ℤ)) Jc hJc
  have hbound : IsBoundedAtImInfty
      (PositiveCuspAction.evenWeightSlash
        (48 * formClassNumber (-(d : ℤ)) + 2) c.chartGL
        (fun z : UpperHalfPlane =>
          ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
            (cmPoleFactor (-(d : ℤ)) z ^ 2 * F z))) := by
    apply isBoundedAtImInfty_of_analytic_qParam_germ one_pos hq hanalyticG Y
    intro z hz hsmall
    exact c.clearedShimuraGerm_qParam_eq_evenWeightSlash
      (-(d : ℤ)) F Jc z (hJq z hz hsmall)
  exact cmCleared_boundedAt_of_representative (-(d : ℤ)) F c.chartGL
    (c.chartGL_det_pos) hanalytic hgerm hbound

end SptClassification
