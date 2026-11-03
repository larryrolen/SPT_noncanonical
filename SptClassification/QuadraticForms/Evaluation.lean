/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.Action
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Scalar extension and upper-half-plane roots of binary forms

An integral form can be evaluated over any commutative ring. Over the complex
numbers, a quadratic with nonzero leading coefficient has at most one root in
the upper half-plane.
-/

public section

namespace SptClassification.BinaryQuadraticForm

/-- Evaluate the integral form after extending its coefficients to a ring. -/
def evaluateOver (R : Type*) [CommRing R] (Q : BinaryQuadraticForm) (x y : R) : R :=
  (Q.a : R) * x ^ 2 + (Q.b : R) * x * y + (Q.c : R) * y ^ 2

/-- The coefficient formula for evaluating a binary form over a commutative ring. -/
theorem evaluateOver_eq (R : Type*) [CommRing R] (Q : BinaryQuadraticForm) (x y : R) :
    evaluateOver R Q x y =
      (Q.a : R) * x ^ 2 + (Q.b : R) * x * y + (Q.c : R) * y ^ 2 := (rfl)

/-- Evaluation at `(z, 1)` as the usual quadratic polynomial. -/
theorem evaluateOver_one (R : Type*) [CommRing R] (Q : BinaryQuadraticForm) (z : R) :
    evaluateOver R Q z 1 = (Q.a : R) * z ^ 2 + (Q.b : R) * z + (Q.c : R) := by
  simp only [evaluateOver_eq, one_pow, mul_one]

theorem evaluateOver_pullback {R : Type*} [CommRing R] (Q : BinaryQuadraticForm)
    (M : Matrix (Fin 2) (Fin 2) ℤ) (x y : R) :
    evaluateOver R (Q.pullback M) x y =
      evaluateOver R Q ((M 0 0 : R) * x + (M 0 1 : R) * y)
        ((M 1 0 : R) * x + (M 1 1 : R) * y) := by
  simp only [evaluateOver, pullback]
  push_cast
  ring

theorem evaluateOver_homogeneous {R : Type*} [CommRing R]
    (Q : BinaryQuadraticForm) (t x y : R) :
    evaluateOver R Q (t * x) (t * y) = t ^ 2 * evaluateOver R Q x y := by
  simp only [evaluateOver]
  ring

theorem four_mul_a_evaluateOver {R : Type*} [CommRing R]
    (Q : BinaryQuadraticForm) (x y : R) :
    4 * (Q.a : R) * evaluateOver R Q x y =
      (2 * (Q.a : R) * x + (Q.b : R) * y) ^ 2 - (Q.discriminant : R) * y ^ 2 := by
  simp only [evaluateOver, discriminant]
  push_cast
  ring

theorem evaluateOver_complex_re (Q : BinaryQuadraticForm) (z : ℂ) :
    (evaluateOver ℂ Q z 1).re =
      (Q.a : ℝ) * (z.re ^ 2 - z.im ^ 2) + (Q.b : ℝ) * z.re + (Q.c : ℝ) := by
  simp [evaluateOver, pow_two, Complex.mul_re, Complex.mul_im]

theorem evaluateOver_complex_im (Q : BinaryQuadraticForm) (z : ℂ) :
    (evaluateOver ℂ Q z 1).im = (2 * (Q.a : ℝ) * z.re + (Q.b : ℝ)) * z.im := by
  simp [evaluateOver, pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem upper_root_unique (Q : BinaryQuadraticForm) (ha : Q.a ≠ 0)
    (z w : UpperHalfPlane) (hz : evaluateOver ℂ Q z 1 = 0)
    (hw : evaluateOver ℂ Q w 1 = 0) : z = w := by
  have haR : (Q.a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hzI := congrArg Complex.im hz
  have hwI := congrArg Complex.im hw
  rw [evaluateOver_complex_im] at hzI hwI
  simp only [Complex.zero_im] at hzI hwI
  change (2 * (Q.a : ℝ) * z.re + (Q.b : ℝ)) * z.im = 0 at hzI
  change (2 * (Q.a : ℝ) * w.re + (Q.b : ℝ)) * w.im = 0 at hwI
  have hzlin := (mul_eq_zero.mp hzI).resolve_right (ne_of_gt z.im_pos)
  have hwlin := (mul_eq_zero.mp hwI).resolve_right (ne_of_gt w.im_pos)
  have hdiff : (2 * (Q.a : ℝ)) * (z.re - w.re) = 0 := by
    linear_combination hzlin - hwlin
  have hre : z.re = w.re := sub_eq_zero.mp
    ((mul_eq_zero.mp hdiff).resolve_left (mul_ne_zero (by norm_num) haR))
  have hzR := congrArg Complex.re hz
  have hwR := congrArg Complex.re hw
  rw [evaluateOver_complex_re] at hzR hwR
  simp only [Complex.zero_re] at hzR hwR
  change (Q.a : ℝ) * (z.re ^ 2 - z.im ^ 2) + (Q.b : ℝ) * z.re + (Q.c : ℝ) = 0 at hzR
  change (Q.a : ℝ) * (w.re ^ 2 - w.im ^ 2) + (Q.b : ℝ) * w.re + (Q.c : ℝ) = 0 at hwR
  rw [hre] at hzR
  have himsq : (Q.a : ℝ) * (z.im ^ 2 - w.im ^ 2) = 0 := by
    linear_combination hwR - hzR
  have hs := (mul_eq_zero.mp himsq).resolve_left haR
  have hf : (z.im - w.im) * (z.im + w.im) = 0 := by nlinarith only [hs]
  have him : z.im = w.im := sub_eq_zero.mp
    ((mul_eq_zero.mp hf).resolve_right (ne_of_gt (add_pos z.im_pos w.im_pos)))
  exact UpperHalfPlane.ext (Complex.ext hre him)

end SptClassification.BinaryQuadraticForm
