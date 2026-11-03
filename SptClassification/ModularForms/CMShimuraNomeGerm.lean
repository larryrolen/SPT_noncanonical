/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ComplexPowerSeries

/-!
# A convergent Shimura Fourier row gives an analytic cusp germ

A single nonzero point of convergence supplies a positive nome radius. This
is the analytic bridge from the high-cusp expansion of the complex lift to
the actual pole-clearing calculation at infinity.
-/

public section

namespace SptClassification

/-- A complex Fourier row converging at a nonzero nome defines an analytic
germ on the smaller open nome disc, with exactly the original coefficients. -/
theorem analytic_nome_germ_of_hasSum_at_nonzero
    (c : ℕ → ℂ) (q₀ : ℂ) (hq₀ : q₀ ≠ 0)
    (hs : HasSum (fun n : ℕ => c n * q₀ ^ n) (∑' n : ℕ, c n * q₀ ^ n)) :
    ∃ J : ℂ → ℂ, (∀ q : ℂ, ‖q‖ < ‖q₀‖ → AnalyticAt ℂ J q) ∧
      ∀ q : ℂ, ‖q‖ < ‖q₀‖ →
        HasSum (fun n : ℕ => c n * q ^ n) (J q) := by
  let P : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c
  let r : NNReal := ⟨‖q₀‖, norm_nonneg q₀⟩
  have hr : (r : ENNReal) ≤ P.radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    convert hs.summable.norm using 1
    ext n
    simp only [P, FormalMultilinearSeries.ofScalars_norm, r,
      NNReal.coe_mk, norm_mul, norm_pow]
    rfl
  have hrpos : (0 : ENNReal) < r := by
    exact_mod_cast (norm_pos_iff.mpr hq₀)
  have hp : HasFPowerSeriesOnBall P.sum P 0 r := by
    constructor
    · exact hr
    · exact hrpos
    · intro q hq
      have hq' : q ∈ Metric.eball (0 : ℂ) P.radius := by
        exact Metric.eball_subset_eball hr hq
      simpa only [zero_add] using P.hasSum hq'
  refine ⟨P.sum, ?_, ?_⟩
  · intro q hq
    apply hp.analyticAt_of_mem
    rw [Metric.mem_eball, edist_lt_coe]
    apply NNReal.coe_lt_coe.mp
    change dist q 0 < ‖q₀‖
    simpa only [dist_zero_right] using hq
  intro q hq
  have hball : q ∈ Metric.eball (0 : ℂ) (r : ENNReal) := by
    rw [Metric.mem_eball, edist_lt_coe]
    apply NNReal.coe_lt_coe.mp
    change dist q 0 < ‖q₀‖
    simpa only [dist_zero_right] using hq
  have hball' : q ∈ Metric.eball (0 : ℂ) P.radius :=
    Metric.eball_subset_eball hr hball
  simpa only [P, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul, mul_comm] using P.hasSum hball'

end SptClassification
