/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.WeightTwoPrimitive
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Vanishing horizontal periods in weight two

The fundamental theorem of calculus turns the periodic primitive into the
vanishing period integral needed for [rolenManuscript, §3]. The statement
does not assume cusp boundedness, so it applies to weakly holomorphic forms
with poles at infinity.
-/

public section

namespace SptClassification

open Complex Set MeasureTheory
open UpperHalfPlane (upperHalfPlaneSet)

/-- Every holomorphic level-one weight-two function has zero horizontal period. -/
theorem weightTwo_period_integral_eq_zero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1 / z) = z ^ 2 * f z)
    {y : ℝ} (hy : 0 < y) :
    (∫ x : ℝ in 0..1, f (x + y * I)) = 0 := by
  obtain ⟨g, hg, hgT⟩ := exists_periodic_primitive_weightTwo hf hT hS
  have hder (x : ℝ) : HasDerivAt (fun t : ℝ => g (t + y * I))
      (f (x + y * I)) x := by
    have hz : 0 < ((x : ℂ) + y * I).im := by simpa using hy
    have h := ((hg ((x : ℂ) + y * I) hz).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const (y * I))).comp_ofReal
    convert! h using 1
    simp
  have hint : IntervalIntegrable (fun x : ℝ => f (x + y * I)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    exact hf.continuousOn.comp (by fun_prop) (by intro x hx; simpa using hy)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hder x) hint]
  have hper := hgT ((y : ℂ) * I) (by simpa using hy)
  simpa [add_comm] using sub_eq_zero.mpr hper

end SptClassification
