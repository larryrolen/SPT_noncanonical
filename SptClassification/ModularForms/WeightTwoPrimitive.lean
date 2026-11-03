/- Assembled by AxiomProver. -/

module

public import SptClassification.ComplexAnalysis.UpperHalfPlanePrimitive
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Periodic primitives of level-one weight-two forms

A primitive of a holomorphic weight-two function is invariant under inversion:
the difference has zero derivative and vanishes at `I`. Its translation
difference is constant and vanishes at the fixed point `ρ` of `ST`. This gives
the analytic period vanishing used in [rolenManuscript, §3], without any
assumption about the Fourier constant coefficient.
-/

public section

namespace SptClassification

open Complex Set
open UpperHalfPlane (upperHalfPlaneSet isOpen_upperHalfPlaneSet)

private theorem eq_of_hasDerivAt_zero_upperHalfPlane {g : ℂ → ℂ}
    (hg : ∀ z : ℂ, 0 < z.im → HasDerivAt g 0 z)
    {z w : ℂ} (hz : 0 < z.im) (hw : 0 < w.im) : g z = g w :=
  isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun z hz => (hg z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hg z hz).deriv) hz hw

/-- Every primitive of a holomorphic weight-two function is invariant under S. -/
theorem weightTwo_primitive_inversion {f g : ℂ → ℂ}
    (hg : ∀ z : ℂ, 0 < z.im → HasDerivAt g (f z) z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1 / z) = z ^ 2 * f z)
    {z : ℂ} (hz : 0 < z.im) : g (-1 / z) = g z := by
  have hd (w : ℂ) (hw : 0 < w.im) :
      HasDerivAt (fun v : ℂ => g (-1 / v) - g v) 0 w := by
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw
    have hwi : 0 < (-1 / w).im := by
      simpa using UpperHalfPlane.im_pnat_div_pos 1 ⟨w, hw⟩
    have hi : HasDerivAt (fun v : ℂ => -1 / v) (1 / w ^ 2) w := by
      have h := ((hasDerivAt_id w).inv hw0).neg
      convert h using 1
      · funext v
        simp [id_eq, div_eq_mul_inv]
      · simp [id_eq, div_eq_mul_inv]
    convert ((hg (-1 / w) hwi).comp w hi).sub (hg w hw) using 1
    · ext v; rfl
    · rw [hS w hw]
      field_simp
      ring
  have he := eq_of_hasDerivAt_zero_upperHalfPlane hd hz (w := I) (by simp)
  exact sub_eq_zero.mp (by simpa using he)

/-- The primitive's translation period vanishes, using the elliptic fixed point of ST. -/
theorem weightTwo_primitive_translation {f g : ℂ → ℂ}
    (hg : ∀ z : ℂ, 0 < z.im → HasDerivAt g (f z) z)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1 / z) = z ^ 2 * f z)
    {z : ℂ} (hz : 0 < z.im) : g (z + 1) = g z := by
  have hd (w : ℂ) (hw : 0 < w.im) :
      HasDerivAt (fun v : ℂ => g (v + 1) - g v) 0 w := by
    have hw1 : 0 < (w + 1).im := by simpa using hw
    convert! ((hg (w + 1) hw1).comp w
      ((hasDerivAt_id w).add_const 1)).sub (hg w hw) using 1
    simp only [hT w hw, mul_one, sub_self]
  let ρ : ℂ := UpperHalfPlane.ρ
  have hρ : 0 < ρ.im := UpperHalfPlane.ρ.im_pos
  have hρ1 : 0 < (ρ + 1).im := by simpa using hρ
  have hρ1_ne : ρ + 1 ≠ 0 := by intro h; simp [h] at hρ1
  have hfix : -1 / (ρ + 1) = ρ := by
    apply (div_eq_iff hρ1_ne).2
    have hs : ρ ^ 2 = -ρ - 1 := UpperHalfPlane.ρ_sq
    linear_combination -hs
  have hbase : g (ρ + 1) = g ρ := by
    simpa [hfix] using (weightTwo_primitive_inversion hg hS hρ1).symm
  have he := eq_of_hasDerivAt_zero_upperHalfPlane hd hz hρ
  exact sub_eq_zero.mp (by simpa [hbase] using he)

/-- A holomorphic function with the actual level-one weight-two generator laws
has a primitive whose translation period is zero. -/
theorem exists_periodic_primitive_weightTwo {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hT : ∀ z : ℂ, 0 < z.im → f (z + 1) = f z)
    (hS : ∀ z : ℂ, 0 < z.im → f (-1 / z) = z ^ 2 * f z) :
    ∃ g : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt g (f z) z) ∧
      ∀ z : ℂ, 0 < z.im → g (z + 1) = g z := by
  obtain ⟨g, hg⟩ := ComplexAnalysis.exists_primitive_upperHalfPlane hf
  exact ⟨g, hg, fun z hz => weightTwo_primitive_translation hg hT hS hz⟩

end SptClassification
