/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMShimuraCuspComparison
public import SptClassification.ModularForms.MeromorphicCusp

/-!
# Pointwise clearing above a cusp height

The actual Fourier germ identifies the removable interior extension with
the original product above a fixed height. This supplies the analytic
comparison used for the integral Fourier row in [rolenManuscript, Section 4,
proof of prop:obstruction]. No value of a totalized lift at a pole is assumed.
-/

public section

namespace SptClassification

open Filter
open scoped Topology

/-- The discriminant times the removable CM extension agrees with the actual
CM polynomial product throughout a sufficiently high cusp region. The same
lift supplies the punctured germs and the convergent integral Fourier row. -/
theorem principalCMShimuraLift_cleared_eq_on_high_cusp (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : d % 24 = 23)
    (J : ℂ → ℂ) (Y : ℝ)
    (hanalytic : AnalyticOnNhd ℂ
      (cmPoleClearedFunction (-(d : ℤ)) J) {w | 0 < w.im})
    (hgerm : ∀ z : UpperHalfPlane,
      (fun w => cmPoleFactor (-(d : ℤ)) w ^ 2 * J w) =ᶠ[𝓝[≠] (z : ℂ)]
        cmPoleClearedFunction (-(d : ℤ)) J)
    (hsum : ∀ z : UpperHalfPlane, Y < z.im →
      HasSum (fun n : ℕ =>
        ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
          Function.Periodic.qParam 1 z ^ n) (J z)) :
    ∃ YF : ℝ, ∀ z : UpperHalfPlane, YF < z.im →
      ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
          cmPoleClearedFunction (-(d : ℤ)) J z =
        cmPoleFactor (-(d : ℤ)) z ^ 2 *
          ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) * J z := by
  let H : ℝ := max Y 0 + 1
  have hH : 0 < H := by dsimp [H]; positivity
  have hY : Y < H := by dsimp [H]; linarith [le_max_left Y 0]
  let z₀ : UpperHalfPlane := ⟨⟨0, H⟩, hH⟩
  have hD : (-(d : ℤ)) % 24 = 1 := by omega
  obtain ⟨_, G, _, hG, _, _, hGq⟩ :=
    principalCMShimuraLift_actual_cusp_germ d hD J Y hsum z₀ hY
  have hq₀ : ‖Function.Periodic.qParam 1 z₀‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos z₀.im_pos
  have hproduct (w : UpperHalfPlane) (hw : Y < w.im)
      (hq : ‖Function.Periodic.qParam 1 w‖ < ‖Function.Periodic.qParam 1 z₀‖) :
      G (Function.Periodic.qParam 1 w) =
        ModularForm.discriminant w ^ (8 * formClassNumber (-(d : ℤ))) *
          cmPoleFactor (-(d : ℤ)) w ^ 2 * J w := by
    simpa only [cmPoleFactor_eq, Polynomial.eval_mul, mul_pow,
      mul_comm, mul_left_comm, mul_assoc] using (hGq w hw hq).2
  refine ⟨H, ?_⟩
  intro z hz
  have hq : ‖Function.Periodic.qParam 1 z‖ < ‖Function.Periodic.qParam 1 z₀‖ := by
    rw [Function.Periodic.norm_qParam, Function.Periodic.norm_qParam]
    apply Real.exp_lt_exp.mpr
    simp only [div_one]
    change -2 * Real.pi * z.im < -2 * Real.pi * H
    nlinarith [Real.pi_pos]
  have heq := cm_cusp_germ_eq_pole_cleared (-(d : ℤ)) J G Y
    (Function.Periodic.qParam 1 z₀) hanalytic hgerm
    (fun q hq => hG q hq (hq.trans hq₀)) hproduct z (hY.trans hz) hq
  rw [← heq, hproduct z (hY.trans hz) hq]
  ring

/-- The same removable extension is bounded at infinity after multiplying
by the discriminant power. This is the infinity input to the four-cusp
construction of the globally holomorphic cleared form. -/
theorem principalCMShimuraLift_cleared_bounded_at_infty (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : d % 24 = 23) (hsq : Squarefree d)
    (J : ℂ → ℂ) (Y : ℝ)
    (hanalytic : AnalyticOnNhd ℂ
      (cmPoleClearedFunction (-(d : ℤ)) J) {w | 0 < w.im})
    (hgerm : ∀ z : UpperHalfPlane,
      (fun w => cmPoleFactor (-(d : ℤ)) w ^ 2 * J w) =ᶠ[𝓝[≠] (z : ℂ)]
        cmPoleClearedFunction (-(d : ℤ)) J)
    (hsum : ∀ z : UpperHalfPlane, Y < z.im →
      HasSum (fun n : ℕ =>
        ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
          Function.Periodic.qParam 1 z ^ n) (J z)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun z : UpperHalfPlane =>
      ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
        cmPoleClearedFunction (-(d : ℤ)) J z) := by
  let H : ℝ := max Y 0 + 1
  have hH : 0 < H := by dsimp [H]; positivity
  have hY : Y < H := by dsimp [H]; linarith [le_max_left Y 0]
  let z₀ : UpperHalfPlane := ⟨⟨0, H⟩, hH⟩
  obtain ⟨G, hG, _, heq⟩ :=
    principalCMShimuraLift_cusp_comparison d hd hsq J Y hanalytic hgerm hsum z₀ hY
  have hq : 0 < ‖Function.Periodic.qParam 1 z₀‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero _)
  exact isBoundedAtImInfty_of_analytic_qParam_germ one_pos hq hG Y heq

end SptClassification
