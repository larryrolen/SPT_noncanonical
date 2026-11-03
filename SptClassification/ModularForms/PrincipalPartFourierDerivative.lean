/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartFourierJ
public import SptClassification.ModularForms.PrincipalPartDerivativeCusp
public import SptClassification.QSeries.ConvergentDerivatives

/-!
# The Fourier core of the derivative of the modular invariant

The holomorphic sum of the integral `j` core agrees locally with `q j(q)` at
nonzero nomes. Differentiating there identifies the integral core of `-Θj`,
including the pole shift in the K-family of [rolenManuscript, §3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Topology

/-- The sum of the integral `j` core, including its removable value at zero. -/
noncomputable def modularJIntegralCoreSum (q : ℂ) : ℂ :=
  ∑' n, (QSeries.modularJIntegralCore.coeff n : ℂ) * q ^ n

private theorem im_invQParam_one_pos {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    0 < (Function.Periodic.invQParam 1 q).im := by
  rw [Function.Periodic.im_invQParam]
  have hlog := Real.log_neg (norm_pos_iff.mpr hq0) hq
  exact mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos (by norm_num) (by positivity)) hlog

/-- The integral `j` core converges throughout the unit disc, including zero. -/
theorem hasSum_modularJIntegralCore_unitDisc {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (QSeries.modularJIntegralCore.coeff n : ℂ) * q ^ n)
      (modularJIntegralCoreSum q) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have hs : Summable (fun n => (QSeries.modularJIntegralCore.coeff n : ℂ) * (0 : ℂ) ^ n) := by
      convert (hasSum_ite_eq (0 : ℕ) (1 : ℂ)).summable using 1
      ext n
      cases n <;> simp
    exact hs.hasSum
  · let τ : UpperHalfPlane := ⟨Function.Periodic.invQParam 1 q, im_invQParam_one_pos hq hq0⟩
    have he : Function.Periodic.qParam 1 τ = q :=
      Function.Periodic.qParam_right_inv one_ne_zero hq0
    simpa only [he, modularJIntegralCoreSum] using (hasSum_modularJIntegralCore τ).summable.hasSum

/-- Away from zero the regular core sum is `q` times the cusp representative of `j`. -/
theorem modularJIntegralCoreSum_eq_mul_cusp {q : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    modularJIntegralCoreSum q = q * levelOneJCusp q := by
  let τ : UpperHalfPlane := ⟨Function.Periodic.invQParam 1 q, im_invQParam_one_pos hq hq0⟩
  have he : Function.Periodic.qParam 1 τ = q :=
    Function.Periodic.qParam_right_inv one_ne_zero hq0
  have hs := (hasSum_modularJIntegralCore τ).tsum_eq
  rw [← levelOneJCusp_qParam τ, he] at hs
  exact hs

/-- The integral core of the negative normalized derivative has its actual analytic sum. -/
theorem hasSum_negative_j_derivative_core (τ : UpperHalfPlane) :
    HasSum (fun n => ((QSeries.modularJIntegralCore -
      QSeries.eulerDerivative QSeries.modularJIntegralCore).coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n)
      (-Function.Periodic.qParam 1 τ * thetaLevelOneJ τ) := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hq : ‖q‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hlocal : modularJIntegralCoreSum =ᶠ[𝓝 q] (fun z => z * levelOneJCusp z) := by
    have hball : q ∈ Metric.ball (0 : ℂ) 1 := by simpa using hq
    filter_upwards [Metric.isOpen_ball.mem_nhds hball, eventually_ne_nhds hq0] with z hz hz0
    exact modularJIntegralCoreSum_eq_mul_cusp (by simpa using hz) hz0
  have hd : deriv modularJIntegralCoreSum q = levelOneJCusp q + q * deriv levelOneJCusp q := by
    simpa using (((hasDerivAt_id q).mul
      (differentiableAt_levelOneJCusp_qParam τ).hasDerivAt).congr_of_eventuallyEq hlocal).deriv
  have hs := QSeries.hasSum_sub_eulerDerivative_of_hasSum
    (fun z hz => hasSum_modularJIntegralCore_unitDisc hz) hq
  have hsum : modularJIntegralCoreSum q - q * deriv modularJIntegralCoreSum q =
      -q * thetaLevelOneJ τ := by
    rw [modularJIntegralCoreSum_eq_mul_cusp hq hq0, hd,
      ← thetaLevelOneJCusp_qParam τ, thetaLevelOneJCusp_eq]
    dsimp only [q]
    ring
  rw [hsum] at hs
  simpa only [QSeries.coeff_negative_j_derivative_core, Int.cast_mul, Int.cast_sub,
    Int.cast_one, Int.cast_natCast] using hs

/-- Absolute convergence of the integral negative-derivative core at every nome. -/
theorem summable_norm_negative_j_derivative_core (τ : UpperHalfPlane) :
    Summable (fun n => ‖((QSeries.modularJIntegralCore -
      QSeries.eulerDerivative QSeries.modularJIntegralCore).coeff n : ℂ) *
      Function.Periodic.qParam 1 τ ^ n‖) :=
  (hasSum_negative_j_derivative_core τ).summable.norm

end SptClassification
