/- Assembled by AxiomProver. -/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Explicit real inequalities for the large-prime discriminant

These inequalities compare the numerical expression arising from the character
bound in [trevino2017] with the square-root discriminant threshold. The proof uses
the tangent bound for the logarithm at512 and exact rational arithmetic.
-/

public section

namespace SptClassification

/-- A rational linear upper bound for the logarithm beyond560. -/
theorem four_log_le_div_twentyTwo {t : ℝ} (ht : 560 ≤ t) :
    4 * Real.log t ≤ t / 22 := by
  have htpos : 0 < t := by linarith
  have hlog2 : Real.log 2 < 347 / 500 := by linarith [Real.log_two_lt_d9]
  have hlog512 : Real.log 512 = 9 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 9
    norm_num at h
    exact h
  have htangent := Real.log_le_sub_one_of_pos (show 0 < t / 512 by positivity)
  rw [Real.log_div htpos.ne' (by norm_num), hlog512] at htangent
  linarith

/-- The fourth root at the cutoff is at least560. -/
theorem fourth_root_ge_fiveHundredSixty {x : ℝ} (hx : 10 ^ 11 ≤ x) :
    560 ≤ x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 560) hx0
    (by norm_num : (0 : ℝ) < 4)).mpr
  norm_num [Real.rpow_natCast]
  linarith

/-- A fourth-root upper bound for the logarithm in the large-prime range. -/
theorem log_le_fourth_root_div_twentyTwo {x : ℝ} (hx : 10 ^ 11 ≤ x) :
    Real.log x ≤ x ^ (1 / 4 : ℝ) / 22 := by
  have hxpos : 0 < x := by linarith
  have h := four_log_le_div_twentyTwo (fourth_root_ge_fiveHundredSixty hx)
  rw [Real.log_rpow hxpos] at h
  linarith

/-- The fourth power of the nonnegative fourth root is the original real number. -/
theorem fourth_root_pow_four {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- The character-bound expression is uniformly less than0.785 of the
square-root threshold throughout the large-prime range. -/
theorem character_bound_lt_ratio_sqrt {x : ℝ} (hx : 10 ^ 11 ≤ x) :
    (2028 / 25 : ℝ) * x ^ (1 / 4 : ℝ) * Real.log x + 24 <
      (157 / 200 : ℝ) * Real.sqrt (24 * x) := by
  let t := x ^ (1 / 4 : ℝ)
  have hx0 : 0 ≤ x := by linarith
  have ht : 560 ≤ t := fourth_root_ge_fiveHundredSixty hx
  have ht0 : 0 ≤ t := by linarith
  have ht4 : t ^ 4 = x := fourth_root_pow_four hx0
  have hlog : Real.log x ≤ t / 22 := log_le_fourth_root_div_twentyTwo hx
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (2028 / 25 : ℝ) * t by positivity)
  have hsqrt : (24 / 5 : ℝ) * t ^ 2 ≤ Real.sqrt (24 * x) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (t ^ 2)]
  change (2028 / 25 : ℝ) * t * Real.log x + 24 < _
  nlinarith [sq_nonneg (t - 560)]

/-- The explicit analytic inequality required to bound the discriminant. -/
theorem effective_discriminant_bound {x : ℝ} (hx : 10 ^ 11 ≤ x) :
    (2028 / 25 : ℝ) * x ^ (1 / 4 : ℝ) * Real.log x + 24 <
      Real.sqrt (24 * x) := by
  have h := character_bound_lt_ratio_sqrt hx
  have hs := Real.sqrt_nonneg (24 * x)
  linarith

/-- The elementary real expression bounding reduced forms is smaller than the
discriminant in the residue range used here. -/
theorem reduced_form_bound_lt_discriminant {d : ℝ} (hd : 23 ≤ d) :
    d / 3 + 2 * Real.sqrt (d / 3) < d := by
  have hnonneg : 0 ≤ d / 3 := by linarith
  have hs : Real.sqrt (d / 3) < d / 3 := by
    apply (Real.sqrt_lt hnonneg hnonneg).mpr
    nlinarith [sq_nonneg (d - 23)]
  linarith

/-- The square-root discriminant threshold is small enough for the degree bound. -/
theorem eight_sqrt_twentyFour_lt {x : ℝ} (hx : 1536 < x) :
    8 * Real.sqrt (24 * x) < x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : Real.sqrt (24 * x) < x / 8 := by
    apply (Real.sqrt_lt (by positivity) (by positivity)).mpr
    nlinarith [mul_pos (show 0 < x by linarith) (show 0 < x - 1536 by linarith)]
  linarith

end SptClassification
