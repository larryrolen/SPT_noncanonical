/- Assembled by AxiomProver. -/

module

public import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Content of integral binary quadratic forms

We retain integral coefficients without imposing primitivity. Scaling a form by
its content multiplies its discriminant by the square of that content.

## Main definitions

* `BinaryQuadraticForm`: the three integral coefficients of a binary quadratic form.
* `BinaryQuadraticForm.content`: the nonnegative gcd of the coefficients.
* `BinaryQuadraticForm.primitivePart`: coefficientwise division by the content.

## References

We use the integral form convention of [ahlgrenAndersen2016], section 2.1.
-/

public section

namespace SptClassification

/-- An integral binary quadratic form `a * X² + b * X * Y + c * Y²`. -/
@[ext] structure BinaryQuadraticForm where
  a : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq

namespace BinaryQuadraticForm

/-- The discriminant in the binary quadratic form convention. -/
@[expose]
def discriminant (Q : BinaryQuadraticForm) : ℤ := Q.b ^ 2 - 4 * Q.a * Q.c

/-- Multiply every coefficient by an integer. -/
@[expose]
def scale (t : ℤ) (Q : BinaryQuadraticForm) : BinaryQuadraticForm :=
  ⟨t * Q.a, t * Q.b, t * Q.c⟩

theorem discriminant_scale (t : ℤ) (Q : BinaryQuadraticForm) :
    (Q.scale t).discriminant = t ^ 2 * Q.discriminant := by
  simp only [discriminant, scale]
  ring

/-- The nonnegative content; the zero form has content zero. -/
def content (Q : BinaryQuadraticForm) : ℕ := Int.gcd Q.a (Int.gcd Q.b Q.c)

/-- Content expressed by the three integral coefficients. -/
theorem content_eq_gcd (Q : BinaryQuadraticForm) :
    Q.content = Int.gcd Q.a (Int.gcd Q.b Q.c) := (rfl)

theorem content_of_a_eq_one (Q : BinaryQuadraticForm) (ha : Q.a = 1) : Q.content = 1 := by
  simp [content, ha]

theorem content_scale (t : ℤ) (Q : BinaryQuadraticForm) :
    (Q.scale t).content = t.natAbs * Q.content := by
  simp [content, scale, Int.gcd, Int.natAbs_mul, Int.natAbs_abs, Nat.gcd_mul_left]

theorem content_dvd_a (Q : BinaryQuadraticForm) : (Q.content : ℤ) ∣ Q.a :=
  Int.gcd_dvd_left _ _

theorem content_dvd_b (Q : BinaryQuadraticForm) : (Q.content : ℤ) ∣ Q.b :=
  (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)

theorem content_dvd_c (Q : BinaryQuadraticForm) : (Q.content : ℤ) ∣ Q.c :=
  (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)

theorem content_pos (Q : BinaryQuadraticForm) (ha : Q.a ≠ 0) : 0 < Q.content := by
  apply Nat.pos_of_ne_zero
  intro h
  have hd := Q.content_dvd_a
  rw [h, Nat.cast_zero, zero_dvd_iff] at hd
  exact ha hd

theorem content_sq_dvd_discriminant (Q : BinaryQuadraticForm) :
    (Q.content : ℤ) ^ 2 ∣ Q.discriminant := by
  obtain ⟨a, ha⟩ := Q.content_dvd_a
  obtain ⟨b, hb⟩ := Q.content_dvd_b
  obtain ⟨c, hc⟩ := Q.content_dvd_c
  refine ⟨b ^ 2 - 4 * a * c, ?_⟩
  simp only [discriminant, ha, hb, hc]
  ring

/-- Coefficientwise division by the content. -/
def primitivePart (Q : BinaryQuadraticForm) : BinaryQuadraticForm :=
  ⟨Q.a / Q.content, Q.b / Q.content, Q.c / Q.content⟩

theorem scale_content_primitivePart (Q : BinaryQuadraticForm) :
    Q.primitivePart.scale Q.content = Q := by
  ext
  · change (Q.content : ℤ) * (Q.a / Q.content) = Q.a
    rw [mul_comm]
    exact Int.ediv_mul_cancel Q.content_dvd_a
  · change (Q.content : ℤ) * (Q.b / Q.content) = Q.b
    rw [mul_comm]
    exact Int.ediv_mul_cancel Q.content_dvd_b
  · change (Q.content : ℤ) * (Q.c / Q.content) = Q.c
    rw [mul_comm]
    exact Int.ediv_mul_cancel Q.content_dvd_c

/-- Dividing a form with nonzero leading coefficient by its content gives a
primitive form. -/
theorem content_primitivePart (Q : BinaryQuadraticForm) (ha : Q.a ≠ 0) :
    Q.primitivePart.content = 1 := by
  have h := congrArg content Q.scale_content_primitivePart
  rw [content_scale] at h
  change Q.content * Q.primitivePart.content = Q.content at h
  apply Nat.eq_of_mul_eq_mul_left (Q.content_pos ha)
  simpa only [mul_one] using h

theorem discriminant_eq_content_sq_mul (Q : BinaryQuadraticForm) :
    Q.discriminant = (Q.content : ℤ) ^ 2 * Q.primitivePart.discriminant := by
  rw [← discriminant_scale, scale_content_primitivePart]

theorem c_pos_of_discriminant_neg (Q : BinaryQuadraticForm)
    (ha : 0 < Q.a) (hD : Q.discriminant < 0) : 0 < Q.c := by
  by_contra h
  have hc : Q.c ≤ 0 := le_of_not_gt h
  have hac := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) hc
  dsimp [discriminant] at hD
  nlinarith [sq_nonneg Q.b]

end BinaryQuadraticForm

end SptClassification
