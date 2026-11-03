/- Assembled by AxiomProver. -/

module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import SptClassification.QSeries.ComplexPowerSeries

/-!
# Uniqueness of Fourier rows known only high in the cusp

Convergence at one nonzero nome gives a positive power-series radius. Equality
above a height gives equality on a punctured disc, and continuity fills its
center. Thus the coefficients are unique without a global convergence premise.
-/

public section

namespace SptClassification

open Filter UpperHalfPlane
open scoped Topology

/-- A single nonzero point of absolute convergence supplies the formal Taylor
series of the sum at zero. -/
theorem hasFPowerSeriesAt_sum_of_hasSum_nonzero (c : ℕ → ℂ) (q₀ a : ℂ)
    (hq₀ : q₀ ≠ 0) (hs : HasSum (fun n => c n * q₀ ^ n) a) :
    HasFPowerSeriesAt (FormalMultilinearSeries.ofScalars ℂ c).sum
      (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
  let P := FormalMultilinearSeries.ofScalars ℂ c
  let r : NNReal := ⟨‖q₀‖, norm_nonneg q₀⟩
  have hr : (r : ENNReal) ≤ P.radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    convert hs.summable.norm using 1
    ext n
    simp only [P, FormalMultilinearSeries.ofScalars_norm, r,
      NNReal.coe_mk, norm_mul, norm_pow]
    rfl
  have hp : HasFPowerSeriesOnBall P.sum P 0 r := by
    constructor
    · exact hr
    · exact_mod_cast (norm_pos_iff.mpr hq₀)
    · intro q hq
      simpa only [zero_add] using P.hasSum (Metric.eball_subset_eball hr hq)
  exact hp.hasFPowerSeriesAt

/-- Two Fourier rows agreeing above a common height have identical coefficients. -/
theorem highCusp_fourierRow_unique (F : UpperHalfPlane → ℂ) (a b : ℕ → ℂ) (Y : ℝ)
    (ha : ∀ τ : UpperHalfPlane, Y < τ.im →
      HasSum (fun n => a n * Function.Periodic.qParam 1 τ ^ n) (F τ))
    (hb : ∀ τ : UpperHalfPlane, Y < τ.im →
      HasSum (fun n => b n * Function.Periodic.qParam 1 τ ^ n) (F τ)) : a = b := by
  let H := max Y 0 + 1
  have hH : 0 < H := by dsimp [H]; positivity
  have hY : Y < H := by dsimp [H]; linarith [le_max_left Y 0]
  let τ₀ : UpperHalfPlane := ⟨⟨0, H⟩, hH⟩
  let P := FormalMultilinearSeries.ofScalars ℂ a
  let Q := FormalMultilinearSeries.ofScalars ℂ b
  have hp : HasFPowerSeriesAt P.sum P 0 :=
    hasFPowerSeriesAt_sum_of_hasSum_nonzero a _ _ (Complex.exp_ne_zero _) (ha τ₀ hY)
  have hq : HasFPowerSeriesAt Q.sum Q 0 :=
    hasFPowerSeriesAt_sum_of_hasSum_nonzero b _ _ (Complex.exp_ne_zero _) (hb τ₀ hY)
  have hsmall : ∀ᶠ q : ℂ in 𝓝 (0 : ℂ), ‖q‖ < Real.exp (-2 * Real.pi * H) := by
    exact (continuous_norm.tendsto 0).eventually
      (Iio_mem_nhds (by simpa using Real.exp_pos (-2 * Real.pi * H)))
  have he : P.sum =ᶠ[𝓝[≠] (0 : ℂ)] Q.sum := by
    filter_upwards [hp.eventually_hasSum.filter_mono nhdsWithin_le_nhds,
      hq.eventually_hasSum.filter_mono nhdsWithin_le_nhds,
      hsmall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hpa hqb hsmall hnonzero
    -- The puncture permits the inverse nome coordinate.
    have hlog : Real.log ‖q‖ < -2 * Real.pi * H := by
      have := Real.log_lt_log (norm_pos_iff.mpr hnonzero) hsmall
      simpa using this
    have hheight : H < (Function.Periodic.invQParam 1 q).im := by
      rw [Function.Periodic.im_invQParam]
      have heq : - (1 : ℝ) / (2 * Real.pi) * Real.log ‖q‖ =
          -Real.log ‖q‖ / (2 * Real.pi) := by ring
      rw [heq, lt_div_iff₀ (by positivity)]
      nlinarith
    let τ : UpperHalfPlane := ⟨Function.Periodic.invQParam 1 q, hH.trans hheight⟩
    have hinv : Function.Periodic.qParam 1 τ = q :=
      Function.Periodic.qParam_right_inv one_ne_zero hnonzero
    have hsa := ha τ (hY.trans hheight)
    have hsb := hb τ (hY.trans hheight)
    rw [hinv] at hsa hsb
    have hpa' : HasSum (fun n => a n * q ^ n) (P.sum q) := by
      simpa [P, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hpa
    have hqb' : HasSum (fun n => b n * q ^ n) (Q.sum q) := by
      simpa [Q, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using hqb
    exact hpa'.unique hsa |>.trans (hqb'.unique hsb).symm
  have hzero : P.sum 0 = Q.sum 0 :=
    tendsto_nhds_unique
      (hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      ((hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  have he' : P.sum =ᶠ[𝓝 (0 : ℂ)] Q.sum := by
    change ∀ᶠ q in 𝓝[≠] (0 : ℂ), P.sum q = Q.sum q at he
    rw [eventually_nhdsWithin_iff] at he
    filter_upwards [he] with q hq
    by_cases h : q = 0
    · simpa [h] using hzero
    · exact hq h
  have heq := hp.eq_formalMultilinearSeries_of_eventually hq he'
  funext n
  simpa [P, Q] using congrArg (fun p => FormalMultilinearSeries.coeff p n) heq

end SptClassification
