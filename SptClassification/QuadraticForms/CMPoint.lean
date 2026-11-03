/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.Evaluation
public import SptClassification.QuadraticForms.LevelSixClasses
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# The CM point of a positive definite form

For negative discriminant `D`, the point has real part `-b/(2a)` and positive
imaginary part `sqrt(-D)/(2a)`. It is characterized as the unique upper-half-plane
root of the form evaluated at `(z,1)`.

## References

We follow [ahlgrenAndersen2016], section 1.
-/

public section

namespace SptClassification

namespace PositiveForm

/-- The upper-half-plane root, with the positive real square root of `-D`. -/
noncomputable def cmPoint {D : ℤ} [Fact (D < 0)] (Q : PositiveForm D) : UpperHalfPlane :=
  ⟨⟨-(Q.b : ℝ) / (2 * (Q.a : ℝ)), Real.sqrt (-(D : ℝ)) / (2 * (Q.a : ℝ))⟩, by
    apply div_pos
    · apply Real.sqrt_pos.mpr
      exact_mod_cast (neg_pos.mpr (Fact.out : D < 0))
    · exact mul_pos (by norm_num) (by exact_mod_cast Q.a_pos)⟩

@[simp] theorem cmPoint_re {D : ℤ} [Fact (D < 0)] (Q : PositiveForm D) :
    Q.cmPoint.re = -(Q.b : ℝ) / (2 * (Q.a : ℝ)) := (rfl)

@[simp] theorem cmPoint_im {D : ℤ} [Fact (D < 0)] (Q : PositiveForm D) :
    Q.cmPoint.im = Real.sqrt (-(D : ℝ)) / (2 * (Q.a : ℝ)) := (rfl)

theorem twice_a_cmPoint_add_b {D : ℤ} [Fact (D < 0)] (Q : PositiveForm D) :
    2 * (Q.a : ℂ) * Q.cmPoint + (Q.b : ℂ) =
      Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ) := by
  have ha : (Q.a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt Q.a_pos)
  apply Complex.ext
  · simp [cmPoint, Complex.mul_re, Complex.mul_im]
    field_simp [ha]
    ring
  · simp [cmPoint, Complex.mul_re, Complex.mul_im]
    field_simp [ha]

/-- The usual quadratic-formula expression, with the positive imaginary square root. -/
theorem cmPoint_eq_formula {D : ℤ} [Fact (D < 0)] (Q : PositiveForm D) :
    (Q.cmPoint : ℂ) = (-(Q.b : ℂ) + Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) /
      (2 * (Q.a : ℂ)) := by
  have ha : (Q.a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt Q.a_pos)
  apply (eq_div_iff (mul_ne_zero (by norm_num) ha)).mpr
  linear_combination Q.twice_a_cmPoint_add_b

theorem evaluateOver_cmPoint {D : ℤ} [Fact (D < 0)] (Q : PositiveForm D) :
    BinaryQuadraticForm.evaluateOver ℂ Q.toBinaryQuadraticForm Q.cmPoint 1 = 0 := by
  have ha : (Q.a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt Q.a_pos)
  have hD : 0 ≤ -(D : ℝ) := by exact_mod_cast (le_of_lt (neg_pos.mpr (Fact.out : D < 0)))
  have hsqrt : (Real.sqrt (-(D : ℝ)) : ℂ) ^ 2 = -(D : ℂ) := by
    exact_mod_cast Real.sq_sqrt hD
  have hsq : (2 * (Q.a : ℂ) * Q.cmPoint + (Q.b : ℂ)) ^ 2 = (D : ℂ) := by
    rw [twice_a_cmPoint_add_b, mul_pow, Complex.I_sq, hsqrt]
    ring
  have h4 : (4 * (Q.a : ℂ)) *
      BinaryQuadraticForm.evaluateOver ℂ Q.toBinaryQuadraticForm Q.cmPoint 1 = 0 := by
    rw [BinaryQuadraticForm.four_mul_a_evaluateOver]
    simp only [one_pow, mul_one, Q.discriminant_eq, hsq, sub_self]
  exact (mul_eq_zero.mp h4).resolve_left (mul_ne_zero (by norm_num) ha)

theorem eq_cmPoint_iff {D : ℤ} [Fact (D < 0)] (Q : PositiveForm D) (z : UpperHalfPlane) :
    z = Q.cmPoint ↔ BinaryQuadraticForm.evaluateOver ℂ Q.toBinaryQuadraticForm z 1 = 0 := by
  constructor
  · rintro rfl
    exact Q.evaluateOver_cmPoint
  · intro hz
    exact Q.toBinaryQuadraticForm.upper_root_unique (ne_of_gt Q.a_pos) z Q.cmPoint hz
      Q.evaluateOver_cmPoint

end PositiveForm

namespace LevelSixForm

/-- The CM point of an oriented level-six form. -/
noncomputable def cmPoint {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) : UpperHalfPlane := Q.toPositiveForm.cmPoint

@[simp] theorem cmPoint_eq_toPositiveForm {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) : Q.cmPoint = Q.toPositiveForm.cmPoint := (rfl)

@[simp] theorem cmPoint_re {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) :
    (Q.cmPoint : ℂ).re = -(Q.b : ℝ) / (2 * (Q.a : ℝ)) := by
  have ha : Q.toPositiveForm.a = Q.a :=
    congrArg BinaryQuadraticForm.a Q.toPositiveForm_toBinaryQuadraticForm
  have hb : Q.toPositiveForm.b = Q.b :=
    congrArg BinaryQuadraticForm.b Q.toPositiveForm_toBinaryQuadraticForm
  change Q.toPositiveForm.cmPoint.re = _
  rw [Q.toPositiveForm.cmPoint_re, ha, hb]

@[simp] theorem cmPoint_im {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) :
    (Q.cmPoint : ℂ).im = Real.sqrt (-(D : ℝ)) / (2 * (Q.a : ℝ)) := by
  have ha : Q.toPositiveForm.a = Q.a :=
    congrArg BinaryQuadraticForm.a Q.toPositiveForm_toBinaryQuadraticForm
  change Q.toPositiveForm.cmPoint.im = _
  rw [Q.toPositiveForm.cmPoint_im, ha]

/-- The quadratic-formula expression for an oriented level-six CM point. -/
theorem cmPoint_eq_formula {D : ℤ} {r : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) :
    (Q.cmPoint : ℂ) = (-(Q.b : ℂ) + Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ)) /
      (2 * (Q.a : ℂ)) := by
  have ha : Q.toPositiveForm.a = Q.a :=
    congrArg BinaryQuadraticForm.a Q.toPositiveForm_toBinaryQuadraticForm
  have hb : Q.toPositiveForm.b = Q.b :=
    congrArg BinaryQuadraticForm.b Q.toPositiveForm_toBinaryQuadraticForm
  change (Q.toPositiveForm.cmPoint : ℂ) = _
  rw [Q.toPositiveForm.cmPoint_eq_formula, ha, hb]

theorem evaluateOver_cmPoint {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r) :
    BinaryQuadraticForm.evaluateOver ℂ Q.toBinaryQuadraticForm Q.cmPoint 1 = 0 :=
  by simpa only [cmPoint, toPositiveForm_toBinaryQuadraticForm] using
    Q.toPositiveForm.evaluateOver_cmPoint

end LevelSixForm

end SptClassification
