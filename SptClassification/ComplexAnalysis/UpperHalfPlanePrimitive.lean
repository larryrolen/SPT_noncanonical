/- Assembled by AxiomProver. -/

module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Holomorphic primitives on the upper half-plane

Rectangular path integrals give a primitive of every holomorphic function on
the upper half-plane. This supplies the analytic input for the weight-two
constant-term argument in [rolenManuscript, §3].
-/

public section

namespace SptClassification.ComplexAnalysis

open Complex Set MeasureTheory Filter
open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)
open Metric
open scoped Topology

private theorem horizontal_intervalIntegrable {f : ℂ → ℂ}
    (hf : ContinuousOn f upperHalfPlaneSet) (a c b : ℝ) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => f (x + b * I)) volume a c := by
  apply ContinuousOn.intervalIntegrable
  exact hf.comp (by fun_prop) (by intro x hx; simpa using hb)

private theorem vertical_intervalIntegrable {f : ℂ → ℂ}
    (hf : ContinuousOn f upperHalfPlaneSet) (a b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    IntervalIntegrable (fun y : ℝ => f (a + y * I)) volume b c := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp (by fun_prop)
  intro y hy
  have : 0 < y := lt_of_lt_of_le (lt_min hb hc) hy.1
  simpa using this

/-- Rectangular path integration in the upper half-plane is additive. -/
theorem wedgeIntegral_add_upperHalfPlane {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    {a z w : ℂ} (ha : 0 < a.im) (hz : 0 < z.im) (hw : 0 < w.im) :
    wedgeIntegral a w f - wedgeIntegral a z f = wedgeIntegral z w f := by
  set I₁ := ∫ x : ℝ in a.re..w.re, f (x + a.im * I)
  set I₂ := I • ∫ y : ℝ in a.im..w.im, f (w.re + y * I)
  set I₃ := ∫ x : ℝ in a.re..z.re, f (x + a.im * I)
  set I₄ := I • ∫ y : ℝ in a.im..z.im, f (z.re + y * I)
  set I₅ := ∫ x : ℝ in z.re..w.re, f (x + z.im * I)
  set I₆ := I • ∫ y : ℝ in z.im..w.im, f (w.re + y * I)
  set I₇ := ∫ x : ℝ in z.re..w.re, f (x + a.im * I)
  set I₈ := I • ∫ y : ℝ in a.im..z.im, f (w.re + y * I)
  have h₁ : I₁ = I₃ + I₇ := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (horizontal_intervalIntegrable hf.continuousOn _ _ _ ha)
      (horizontal_intervalIntegrable hf.continuousOn _ _ _ ha)).symm
  have h₂ : I₂ = I₈ + I₆ := by
    dsimp [I₂, I₈, I₆]
    rw [← mul_add]
    congr 1
    exact (intervalIntegral.integral_add_adjacent_intervals
      (vertical_intervalIntegrable hf.continuousOn _ _ _ ha hz)
      (vertical_intervalIntegrable hf.continuousOn _ _ _ hz hw)).symm
  have h₀ : I₇ - I₅ + I₈ - I₄ = 0 := by
    have hrect : Rectangle (z.re + a.im * I) (w.re + z.im * I) ⊆
        upperHalfPlaneSet :=
      (convex_halfSpace_im_gt (r := 0)).rectangle_subset (by simpa using ha) (by simpa using hz)
        (by simpa using hz) (by simpa using ha)
    simpa [I₇, I₅, I₈, I₄, ← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] using
      hf.isConservativeOn (z.re + a.im * I) (w.re + z.im * I) hrect
  change I₁ + I₂ - (I₃ + I₄) = I₅ + I₆
  linear_combination h₁ + h₂ + h₀

/-- Integrating from any fixed upper-half-plane point gives a holomorphic primitive. -/
theorem hasDerivAt_wedgeIntegral_upperHalfPlane {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    {a z : ℂ} (ha : 0 < a.im) (hz : 0 < z.im) :
    HasDerivAt (fun w => wedgeIntegral a w f) (f z) z := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_upperHalfPlaneSet z hz
  have hlocal := (hf.mono hball).isConservativeOn.hasDerivAt_wedgeIntegral
    (hf.continuousOn.mono hball) (mem_ball_self hr)
  have heq : (fun w => wedgeIntegral a w f) =ᶠ[𝓝 z]
      (fun w => wedgeIntegral z w f + wedgeIntegral a z f) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
    have := wedgeIntegral_add_upperHalfPlane hf ha hz hw
    exact sub_eq_iff_eq_add.mp this
  exact (hlocal.add_const _).congr_of_eventuallyEq heq

/-- Every holomorphic function on the upper half-plane has an actual primitive. -/
theorem exists_primitive_upperHalfPlane {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) :
    ∃ g : ℂ → ℂ, ∀ z : ℂ, 0 < z.im → HasDerivAt g (f z) z :=
  ⟨fun z => wedgeIntegral I z f, fun z hz =>
    hasDerivAt_wedgeIntegral_upperHalfPlane hf (by simp) hz⟩

end SptClassification.ComplexAnalysis
