/- Assembled by AxiomProver. -/

module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.Ring

/-!
# Convergent complex power series on the unit disc

Coefficient uniqueness and Cauchy multiplication connect holomorphic Taylor
series with integral formal series in the eta comparison of [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

/-- A coefficient series that sums throughout the unit disc is an analytic power series there. -/
theorem hasFPowerSeriesOnBall_of_hasSum {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => c n * q ^ n) (f q)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 1 := by
  constructor
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    lift r to NNReal using hr.ne_top
    apply FormalMultilinearSeries.le_radius_of_summable
    simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using
      (hc r (by simpa using hr)).summable.norm
  · simp
  · intro q hq
    rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hq
    simpa [mul_comm] using hc q hq

/-- Coefficient sequences with the same sums throughout the unit disc agree. -/
theorem coefficients_eq_of_hasSum {c d : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => c n * q ^ n) (f q))
    (hd : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => d n * q ^ n) (f q)) : c = d := by
  have he := (hasFPowerSeriesOnBall_of_hasSum hc).hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesOnBall_of_hasSum hd).hasFPowerSeriesAt
  funext n
  simpa using congrArg (fun p => FormalMultilinearSeries.coeff p n) he

/-- The constant formal series one sums to one at every complex argument. -/
theorem hasSum_complexPowerSeries_one (q : ℂ) :
    HasSum (fun n => (1 : PowerSeries ℂ).coeff n * q ^ n) 1 := by
  simpa +contextual [PowerSeries.coeff_one] using hasSum_ite_eq (0 : ℕ) (1 : ℂ)

/-- Multiplying convergent complex formal series multiplies their analytic sums. -/
theorem hasSum_complexPowerSeries_mul (F G : PowerSeries ℂ) (q a b : ℂ)
    (hF : HasSum (fun n => F.coeff n * q ^ n) a)
    (hG : HasSum (fun n => G.coeff n * q ^ n) b) :
    HasSum (fun n => (F * G).coeff n * q ^ n) (a * b) := by
  have hc (n : ℕ) : (F * G).coeff n * q ^ n =
      ∑ p ∈ Finset.antidiagonal n, (F.coeff p.1 * q ^ p.1) * (G.coeff p.2 * q ^ p.2) := by
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.mem_antidiagonal.mp hp, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm
    hF.summable.norm hG.summable.norm
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    hF.summable.norm hG.summable.norm
  rw [hF.tsum_eq, hG.tsum_eq] at he
  simpa only [hc, ← he] using hs.of_norm.hasSum

end SptClassification.QSeries
