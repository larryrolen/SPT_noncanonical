/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.ShortTateParameter
public import Mathlib.Analysis.Complex.Basic

/-!
# The limiting marked Tate coordinate

This is the algebra and continuity step from the classical degenerations of
`wp(1/6)`, `wp'(1/6)/2`, and `-g₂/4`. It does not assume or assert those
analytic degenerations for the actual period lattice.
-/

public section

namespace SptClassification.LevelSixWeierstrass

/-- Changing the scale of a short equation preserves its marked parameter. -/
theorem shortTateParameter_scale {F : Type*} [Field F] [CharZero F]
    (a x y k : F) (hy : y ≠ 0) (hk : k ≠ 0) :
    shortTateParameter (k ^ 4 * a) (k ^ 2 * x) (k ^ 3 * y) =
      shortTateParameter a x y := by
  simp only [shortTateParameter_eq]
  field_simp
  <;> ring

/-- The trigonometric degeneration evaluates to the width-one cusp. -/
theorem shortTateParameter_cusp_value {F : Type*} [Field F] [CharZero F]
    (r : F) (hr : r ^ 2 = 3) :
    shortTateParameter (-1 / 3) (11 / 3) (-4 * r) = -1 / 9 := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  have hr4 : r ^ 4 = 9 := by calc
    r ^ 4 = (r ^ 2) ^ 2 := by ring
    _ = 9 := by rw [hr]; norm_num
  simp only [shortTateParameter_eq]
  field_simp
  <;> ring_nf
  <;> norm_num [hr, hr4]

/-- Algebraic evaluation in an arbitrary nonzero period scale. -/
theorem shortTateParameter_scaled_cusp_value (k r : ℂ)
    (hk : k ≠ 0) (hr : r ^ 2 = 3) :
    shortTateParameter (-k ^ 4 / 3) (11 * k ^ 2 / 3) (-4 * r * k ^ 3) = -1 / 9 := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  have h := shortTateParameter_scale (-1 / 3) (11 / 3) (-4 * r) k
    (mul_ne_zero (by norm_num) hr0) hk
  convert h.trans (shortTateParameter_cusp_value r hr) using 1 <;> congr 1 <;> ring

/-- Separate limits of the short coefficients and marked coordinates imply
the marked parameter limit. The nonzero limiting y-coordinate makes division
continuous. The hypotheses are the analytic inputs still needed from the
actual Weierstrass functions. -/
theorem tendsto_shortTateParameter_cusp {α : Type*} {l : Filter α}
    {a x y : α → ℂ} (k r : ℂ) (hk : k ≠ 0) (hr : r ^ 2 = 3)
    (ha : Filter.Tendsto a l (nhds (-k ^ 4 / 3)))
    (hx : Filter.Tendsto x l (nhds (11 * k ^ 2 / 3)))
    (hy : Filter.Tendsto y l (nhds (-4 * r * k ^ 3))) :
    Filter.Tendsto (fun z => shortTateParameter (a z) (x z) (y z)) l (nhds (-1 / 9)) := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  have hy0 : -4 * r * k ^ 3 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hr0) (pow_ne_zero _ hk)
  have hs := ((hx.pow 2).const_mul 3 |>.add ha).div (hy.const_mul 2)
    (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hy0)
  have h := Filter.Tendsto.sub (tendsto_const_nhds (x := (1 : ℂ)))
    ((hs.mul ((hx.const_mul 3).sub (hs.pow 2))).div hy hy0)
  change Filter.Tendsto (fun z => 1 -
    ((3 * x z ^ 2 + a z) / (2 * y z)) *
      (3 * x z - ((3 * x z ^ 2 + a z) / (2 * y z)) ^ 2) / y z) l
    (nhds (1 - ((3 * (11 * k ^ 2 / 3) ^ 2 + -k ^ 4 / 3) /
      (2 * (-4 * r * k ^ 3))) * (3 * (11 * k ^ 2 / 3) -
      ((3 * (11 * k ^ 2 / 3) ^ 2 + -k ^ 4 / 3) /
      (2 * (-4 * r * k ^ 3))) ^ 2) / (-4 * r * k ^ 3))) at h
  simp only [← shortTateParameter_eq] at h
  simpa only [shortTateParameter_scaled_cusp_value k r hk hr] using h

end SptClassification.LevelSixWeierstrass
