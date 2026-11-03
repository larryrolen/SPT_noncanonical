/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ComplexPowerSeries
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Euler derivatives of convergent coefficient series

Termwise differentiation on the unit disc supplies the analytic meaning of the
formal Euler derivative used in the principal parts of [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

/-- Multiplication by the index corresponds to the Euler derivative of the sum. -/
theorem hasSum_eulerDerivative_of_hasSum {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => c n * z ^ n) (f z))
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (n : ℂ) * c n * q ^ n) (q * deriv f q) := by
  have hp := hasFPowerSeriesOnBall_of_hasSum hc
  have hball : q ∈ Metric.eball (0 : ℂ) 1 := by
    simpa only [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one,
      mem_ball_zero_iff] using hq
  have hs := (ContinuousLinearMap.apply ℂ ℂ q).hasSum (hp.fderiv.hasSum hball)
  have hcoeff (n : ℕ) :
      ((FormalMultilinearSeries.ofScalars ℂ c).derivSeries.coeff n) q =
        q * ((n + 1 : ℕ) : ℂ) * c (n + 1) := by
    calc
      _ = q * ((FormalMultilinearSeries.ofScalars ℂ c).derivSeries.coeff n) 1 := by
        simpa only [smul_eq_mul, mul_one] using
          ((FormalMultilinearSeries.ofScalars ℂ c).derivSeries.coeff n).map_smul q (1 : ℂ)
      _ = _ := by
        rw [FormalMultilinearSeries.derivSeries_coeff_one,
          FormalMultilinearSeries.coeff_ofScalars]
        simp only [nsmul_eq_mul]
        ring
  have he : (fderiv ℂ f q) q = q * deriv f q := by
    simpa only [deriv, smul_eq_mul, mul_one] using (fderiv ℂ f q).map_smul q (1 : ℂ)
  have ht : HasSum (fun n => ((n + 1 : ℕ) : ℂ) * c (n + 1) * q ^ (n + 1))
      (q * deriv f q) := by
    convert hs using 1
    · ext n
      simp only [ContinuousLinearMap.apply_apply,
        FormalMultilinearSeries.apply_eq_pow_smul_coeff, map_smul,
        smul_eq_mul, hcoeff]
      ring
    · simp [he]
  simpa using (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℂ) * c n * q ^ n) 1).mp ht

/-- The coefficient sequence `(1-n)cₙ` sums to the sum minus its Euler derivative. -/
theorem hasSum_sub_eulerDerivative_of_hasSum {c : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => c n * z ^ n) (f z))
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (1 - (n : ℂ)) * c n * q ^ n) (f q - q * deriv f q) := by
  convert (hc q hq).sub (hasSum_eulerDerivative_of_hasSum hc hq) using 1
  ext n
  ring

end SptClassification.QSeries
