/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixSerreExpansion
import all SptClassification.ModularForms.LevelSixSerreExpansion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Quotient calculus for the Laurent Euler operator -/

public noncomputable section
namespace SptClassification.LevelSixSerreExpansion

variable (K : Type*) [Field K]

@[simp] theorem theta_coeff (f : LaurentSeries K) (n : ℤ) :
    (theta K f).coeff n = (n : K) * f.coeff n := by
  simp [theta, HahnSeries.coeff_single_mul, LaurentSeries.derivative,
    LaurentSeries.hasseDeriv_coeff, zsmul_eq_mul]

theorem theta_support_subset (f : LaurentSeries K) :
    (theta K f).support ⊆ f.support := by
  intro n hn
  simp only [HahnSeries.mem_support, theta_coeff, ne_eq, mul_eq_zero, not_or] at hn
  exact hn.2

theorem theta_mul (f g : LaurentSeries K) :
    theta K (f * g) = theta K f * g + f * theta K g := by
  ext n
  rw [theta_coeff, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_left' f.isPWO_support (theta_support_subset K f),
    HahnSeries.coeff_mul_right' g.isPWO_support (theta_support_subset K g),
    HahnSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have he : ij.1 + ij.2 = n := (Finset.mem_antidiagonal.mp hij).2.2
  rw [theta_coeff, theta_coeff, ← he, Int.cast_add]
  ring

/-- Denominator nonvanishing is explicit in the Laurent quotient rule. -/
theorem theta_div (f g : LaurentSeries K) (hg : g ≠ 0) :
    theta K (f / g) = theta K f / g - f * theta K g / g ^ 2 := by
  have h := theta_mul K (f / g) g
  rw [div_mul_cancel₀ f hg] at h
  field_simp [hg] at h ⊢
  linear_combination -h

end SptClassification.LevelSixSerreExpansion
