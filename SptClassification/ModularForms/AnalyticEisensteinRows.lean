/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.AnalyticLaurentProducts
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Rational Fourier rows of normalized Eisenstein series

For even weight at least four, the normalized level-one Eisenstein form has
the rational Bernoulli/divisor-sum coefficients in Mathlib's q-expansion
[rolenManuscript, §2, (2.5)]. This module retains the full rational row
before any reduction modulo a prime.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- Rational coefficient of the normalized level-one Eisenstein series. -/
noncomputable def normalizedEisensteinRationalCoefficient (k n : ℕ) : ℚ :=
  if n = 0 then 1 else
    -(2 * k / bernoulli k) * (ArithmeticFunction.sigma (k - 1) n)

/-- Every positive coefficient is an integer multiple of the first one. -/
theorem normalizedEisensteinRationalCoefficient_eq_first_mul (k n : ℕ)
    (hn : n ≠ 0) :
    normalizedEisensteinRationalCoefficient k n =
      normalizedEisensteinRationalCoefficient k 1 *
        (ArithmeticFunction.sigma (k - 1) n : ℚ) := by
  simp [normalizedEisensteinRationalCoefficient, hn]

@[simp] theorem normalizedEisensteinRationalCoefficient_zero (k : ℕ) :
    normalizedEisensteinRationalCoefficient k 0 = 1 := by
  simp [normalizedEisensteinRationalCoefficient]

/-- Its ordinary rational power series. -/
noncomputable def normalizedEisensteinRationalSeries (k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (normalizedEisensteinRationalCoefficient k)

@[simp] theorem normalizedEisensteinRationalSeries_coeff (k n : ℕ) :
    (normalizedEisensteinRationalSeries k).coeff n =
      normalizedEisensteinRationalCoefficient k n := by
  simp [normalizedEisensteinRationalSeries]

theorem normalizedEisensteinRationalCoefficient_cast
    {k : ℕ} (hk : 3 ≤ k) (heven : Even k) (n : ℕ) :
    (normalizedEisensteinRationalCoefficient k n : ℂ) =
      (qExpansion 1 (ModularForm.E hk)).coeff n := by
  rw [EisensteinSeries.E_qExpansion_coeff hk heven n]
  by_cases hn : n = 0
  · simp [normalizedEisensteinRationalCoefficient, hn]
  · simp [normalizedEisensteinRationalCoefficient, hn]

/-- The rational row converges to the actual normalized Eisenstein form at
every upper-half-plane point. -/
theorem normalizedEisensteinRationalSeries_hasSum
    {k : ℕ} (hk : 3 ≤ k) (heven : Even k) (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ =>
      ((normalizedEisensteinRationalSeries k).coeff n : ℂ) *
        Function.Periodic.qParam 1 τ ^ n)
      (ModularForm.E hk τ) := by
  simpa only [normalizedEisensteinRationalSeries_coeff,
    normalizedEisensteinRationalCoefficient_cast hk heven] using
      ModularForm.hasSum_qExpansion (ModularForm.E hk)
        one_pos one_mem_strictPeriods_SL τ

end SptClassification
