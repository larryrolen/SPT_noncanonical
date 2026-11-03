/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMShimuraCuspGerm
public import SptClassification.ModularForms.CMAnalyticTransformation

/-!
# Comparing the actual cusp germ with the interior CM extension

The high-cusp Fourier row gives an analytic germ in the nome. The interior
pole-cleared lift is a different analytic extension. Their punctured germs
agree after multiplication by the actual discriminant power, so continuity
identifies their values on the high cusp.
-/

public section

namespace SptClassification

open Filter
open scoped Topology

/-- Equality of the cusp germ and the interior extension is obtained from
their common punctured germ. The discriminant power is retained because the
infinity chart clears a further cusp pole. -/
theorem cm_cusp_germ_eq_pole_cleared (D : ℤ) [Fact (D < 0)]
    (F G : ℂ → ℂ) (Y : ℝ) (q₀ : ℂ)
    (hanalytic : AnalyticOnNhd ℂ (cmPoleClearedFunction D F) {w | 0 < w.im})
    (hgerm : ∀ z : UpperHalfPlane,
      (fun w => cmPoleFactor D w ^ 2 * F w) =ᶠ[𝓝[≠] (z : ℂ)]
        cmPoleClearedFunction D F)
    (hG : ∀ q : ℂ, ‖q‖ < ‖q₀‖ → AnalyticAt ℂ G q)
    (hGq : ∀ w : UpperHalfPlane, Y < w.im →
      ‖Function.Periodic.qParam 1 w‖ < ‖q₀‖ →
      G (Function.Periodic.qParam 1 w) =
        ModularForm.discriminant w ^ (8 * formClassNumber D) *
          cmPoleFactor D w ^ 2 * F w)
    (z : UpperHalfPlane) (hzY : Y < z.im)
    (hzq : ‖Function.Periodic.qParam 1 z‖ < ‖q₀‖) :
    G (Function.Periodic.qParam 1 z) =
      ModularForm.discriminant z ^ (8 * formClassNumber D) *
        cmPoleClearedFunction D F z := by
  have hqcont : ContinuousAt (fun w : UpperHalfPlane =>
      Function.Periodic.qParam 1 w) z := by
    unfold Function.Periodic.qParam
    fun_prop
  have hGcont : ContinuousAt (fun w : UpperHalfPlane =>
      G (Function.Periodic.qParam 1 w)) z := by
    change ContinuousAt (G ∘ (fun w : UpperHalfPlane =>
      Function.Periodic.qParam 1 w)) z
    exact ContinuousAt.comp (f := fun w : UpperHalfPlane =>
      Function.Periodic.qParam 1 w) (hG _ hzq).continuousAt hqcont
  have hqone : ‖Function.Periodic.qParam 1 z‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos z.im_pos
  have hdiscCont : ContinuousAt (fun w : UpperHalfPlane =>
      ModularForm.discriminant w) z := by
    have heq : (fun w : UpperHalfPlane => ModularForm.discriminant w) =
        (fun w : UpperHalfPlane => Function.Periodic.qParam 1 w *
          etaEulerProduct (Function.Periodic.qParam 1 w) ^ 24) := by
      funext w
      exact discriminant_eq_etaEulerProduct w
    rw [heq]
    have heta : ContinuousAt (fun w : UpperHalfPlane =>
        etaEulerProduct (Function.Periodic.qParam 1 w)) z := by
      change ContinuousAt (etaEulerProduct ∘ (fun w : UpperHalfPlane =>
        Function.Periodic.qParam 1 w)) z
      exact ContinuousAt.comp (f := fun w : UpperHalfPlane =>
        Function.Periodic.qParam 1 w)
        (analyticAt_etaEulerProduct hqone).continuousAt hqcont
    exact hqcont.mul (heta.pow 24)
  have hclearedCont : ContinuousAt (fun w : UpperHalfPlane =>
      cmPoleClearedFunction D F w) z :=
    (hanalytic z z.im_pos).continuousAt.comp
      UpperHalfPlane.continuous_coe.continuousAt
  have hrightCont : ContinuousAt (fun w : UpperHalfPlane =>
      ModularForm.discriminant w ^ (8 * formClassNumber D) *
        cmPoleClearedFunction D F w) z :=
    (hdiscCont.pow _).mul hclearedCont
  have hYnear : ∀ᶠ w : UpperHalfPlane in 𝓝 z, Y < w.im :=
    (show ContinuousAt (fun w : UpperHalfPlane => w.im) z by fun_prop).eventually
      (Ioi_mem_nhds hzY)
  have hqnear : ∀ᶠ w : UpperHalfPlane in 𝓝 z,
      ‖Function.Periodic.qParam 1 w‖ < ‖q₀‖ :=
    hqcont.norm.eventually (Iio_mem_nhds hzq)
  have heq : (fun w : UpperHalfPlane => G (Function.Periodic.qParam 1 w)) =ᶠ[𝓝[≠] z]
      (fun w => ModularForm.discriminant w ^ (8 * formClassNumber D) *
        cmPoleClearedFunction D F w) := by
    filter_upwards [hYnear.filter_mono nhdsWithin_le_nhds,
      hqnear.filter_mono nhdsWithin_le_nhds,
      upperHalfPlane_punctured_germ z (hgerm z)] with w hwY hwq hwg
    rw [hGq w hwY hwq, ← hwg]
    ring
  exact tendsto_nhds_unique_of_eventuallyEq
    (hGcont.mono_left nhdsWithin_le_nhds)
    (hrightCont.mono_left nhdsWithin_le_nhds) heq

/-- The actual principal Weil lift has an analytic infinity-cusp extension
after clearing its oriented CM poles and the `8h` discriminant pole. On its
overlap with the high cusp, this is the interior analytic extension supplied
by the Borcherds lift. No global integral descent is asserted here.
[rolenManuscript, Section 4, equations (J) and (hasse)] -/
theorem principalCMShimuraLift_cusp_comparison (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : d % 24 = 23) (hsq : Squarefree d)
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
    (z₀ : UpperHalfPlane) (hz₀ : Y < z₀.im) :
    ∃ G : ℂ → ℂ,
      AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      ∀ z : UpperHalfPlane, Y < z.im →
        ‖Function.Periodic.qParam 1 z‖ < ‖Function.Periodic.qParam 1 z₀‖ →
        G (Function.Periodic.qParam 1 z) =
          ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
            cmPoleClearedFunction (-(d : ℤ)) F z := by
  have hD : (-(d : ℤ)) % 24 = 1 := by
    omega
  obtain ⟨J, G, hJ, hG, hJ0, hG0, hGq⟩ :=
    principalCMShimuraLift_actual_cusp_germ d hD F Y hsum z₀ hz₀
  have hq₀ : ‖Function.Periodic.qParam 1 z₀‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos z₀.im_pos
  have hGanalytic : AnalyticAt ℂ G 0 :=
    hG 0 (by
      have hne : Function.Periodic.qParam 1 z₀ ≠ 0 := Complex.exp_ne_zero _
      simpa only [norm_zero] using (norm_pos_iff.mpr hne)) (by simp)
  refine ⟨G, hGanalytic, hG0, ?_⟩
  intro z hz hq
  apply cm_cusp_germ_eq_pole_cleared (-(d : ℤ)) F G Y
    (Function.Periodic.qParam 1 z₀) hanalytic hgerm
  · intro q hq'
    exact hG q hq' (lt_trans hq' hq₀)
  · intro w hwY hwq
    have h := (hGq w hwY hwq).2
    simpa only [cmPoleFactor_eq, Polynomial.eval_mul, mul_pow,
      mul_comm, mul_left_comm, mul_assoc] using h
  · exact hz
  · exact hq

/-- The independent complex lift and its normalized infinity-cusp extension
are obtained from the actual principal Weil input. The extension agrees with
the interior pole clearing on their common high-cusp domain. -/
theorem principalCMShimuraLift_with_cusp_comparison (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : d % 24 = 23) (hsq : Squarefree d) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ (cmPoleClearedFunction (-(d : ℤ)) F) {w | 0 < w.im} ∧
      (∀ (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane),
        cmPoleClearedFunction (-(d : ℤ)) F
          ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
          UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ
            (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ 4 *
            cmPoleClearedFunction (-(d : ℤ)) F z) ∧
      ∃ Y : ℝ,
        (∀ z : UpperHalfPlane, Y < z.im →
          HasSum (fun n : ℕ =>
            ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
              Function.Periodic.qParam 1 z ^ n) (F z)) ∧
        ∀ z₀ : UpperHalfPlane, Y < z₀.im →
          ∃ G : ℂ → ℂ,
            AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
            ∀ z : UpperHalfPlane, Y < z.im →
              ‖Function.Periodic.qParam 1 z‖ < ‖Function.Periodic.qParam 1 z₀‖ →
              G (Function.Periodic.qParam 1 z) =
                ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
                  cmPoleClearedFunction (-(d : ℤ)) F z := by
  obtain ⟨F, hA, hT, _, hGerm, Y, hSum⟩ := principalCMShimuraLift_cleared d hd hsq
  refine ⟨F, hA, hT, Y, hSum, ?_⟩
  intro z₀ hz₀
  exact principalCMShimuraLift_cusp_comparison d hd hsq F Y
    hA hGerm hSum z₀ hz₀

end SptClassification
