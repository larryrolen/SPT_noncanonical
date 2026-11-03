/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoPeriod
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The constant coefficient after clearing a weight-two cusp pole

Multiplication by `q^M` moves the constant Laurent coefficient to Taylor index
`M`. The coefficient integral then reduces to the horizontal period of the
original weight-two function, which vanishes. Only the function after clearing
the pole is required to be bounded at infinity [rolenManuscript, §3].
-/

public section

namespace SptClassification

open Complex UpperHalfPlane
open scoped Manifold

/-- The Taylor coefficient at the pole-clearing index of a weight-two function
vanishes. The original function may have a pole at the cusp. -/
theorem weightTwo_poleCleared_coefficient_eq_zero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1 / z) = z ^ 2 * f z)
    (M : ℕ) {F : UpperHalfPlane → ℂ}
    (hF : ∀ τ : UpperHalfPlane, F τ = Function.Periodic.qParam 1 τ ^ M * f τ)
    (hFper : Function.Periodic (F ∘ ofComplex) 1)
    (hFhol : MDiff F) (hFbdd : IsBoundedAtImInfty F) :
    (qExpansion 1 F).coeff M = 0 := by
  rw [qExpansion_coeff_eq_intervalIntegral (by norm_num : (0 : ℝ) < 1)
    hFper hFhol hFbdd M (by norm_num : (0 : ℝ) < 1)]
  simp only [Complex.ofReal_one, div_one, one_mul]
  convert weightTwo_period_integral_eq_zero hf hT hS (by norm_num : (0 : ℝ) < 1)
    using 1
  apply intervalIntegral.integral_congr
  intro x hx
  dsimp only
  rw [hF]
  have hq : Function.Periodic.qParam 1 ((x : ℂ) + Complex.I) ≠ 0 :=
    Complex.exp_ne_zero _
  dsimp
  field_simp [hq]

end SptClassification
