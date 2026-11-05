/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Unimodular changes of variables

Pullback by a matrix acts contravariantly on integral binary quadratic forms.
Using the inverse matrix gives the usual left action of `SL(2, ℤ)`. Both the
discriminant and the content are invariant under this action.

## References

The left-action convention follows [ahlgrenAndersen2016], equation (2.2).
-/

@[expose] public section

namespace SptClassification.BinaryQuadraticForm

/-- Substitution of the linear variables given by a two-by-two matrix. -/
@[expose]
def pullback (Q : BinaryQuadraticForm) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    BinaryQuadraticForm where
  a := Q.a * M 0 0 ^ 2 + Q.b * M 0 0 * M 1 0 + Q.c * M 1 0 ^ 2
  b := 2 * Q.a * M 0 0 * M 0 1 + Q.b * (M 0 0 * M 1 1 + M 0 1 * M 1 0) +
    2 * Q.c * M 1 0 * M 1 1
  c := Q.a * M 0 1 ^ 2 + Q.b * M 0 1 * M 1 1 + Q.c * M 1 1 ^ 2

@[simp] theorem pullback_one (Q : BinaryQuadraticForm) : Q.pullback 1 = Q := by
  ext <;> simp [pullback]

theorem pullback_mul (Q : BinaryQuadraticForm) (M N : Matrix (Fin 2) (Fin 2) ℤ) :
    (Q.pullback M).pullback N = Q.pullback (M * N) := by
  ext <;> simp [pullback, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem pullback_scale (Q : BinaryQuadraticForm) (t : ℤ)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (Q.scale t).pullback M = (Q.pullback M).scale t := by
  ext <;> simp [pullback, scale] <;> ring

theorem discriminant_pullback (Q : BinaryQuadraticForm) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (Q.pullback M).discriminant = M.det ^ 2 * Q.discriminant := by
  simp only [discriminant, pullback, Matrix.det_fin_two]
  ring

/-- Integral substitution cannot remove a common coefficient divisor. -/
theorem content_dvd_pullback (Q : BinaryQuadraticForm) (M : Matrix (Fin 2) (Fin 2) ℤ) :
    Q.content ∣ (Q.pullback M).content := by
  have h := congrArg (fun P : BinaryQuadraticForm => (P.pullback M).content)
    Q.scale_content_primitivePart
  rw [pullback_scale, content_scale] at h
  change Q.content * (Q.primitivePart.pullback M).content = (Q.pullback M).content at h
  exact ⟨_, h.symm⟩

/-- Left action by substitution with the inverse unimodular matrix. -/
@[expose]
def transform (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (Q : BinaryQuadraticForm) :
    BinaryQuadraticForm := Q.pullback (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ)

@[simp] theorem transform_one (Q : BinaryQuadraticForm) : transform 1 Q = Q := by
  simp [transform]

theorem transform_mul (g h : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : BinaryQuadraticForm) : transform (g * h) Q = transform g (transform h Q) := by
  simp only [transform, mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, pullback_mul]

@[simp] theorem transform_inv_transform (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : BinaryQuadraticForm) : transform g⁻¹ (transform g Q) = Q := by
  rw [← transform_mul, inv_mul_cancel, transform_one]

instance unimodularAction : MulAction (Matrix.SpecialLinearGroup (Fin 2) ℤ)
    BinaryQuadraticForm where
  smul := transform
  one_smul := transform_one
  mul_smul := transform_mul

theorem discriminant_transform (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : BinaryQuadraticForm) : (transform g Q).discriminant = Q.discriminant := by
  rw [transform, discriminant_pullback, (g⁻¹).property]
  simp

theorem content_dvd_transform (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : BinaryQuadraticForm) : Q.content ∣ (transform g Q).content :=
  content_dvd_pullback Q _

theorem content_transform (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (Q : BinaryQuadraticForm) : (transform g Q).content = Q.content := by
  apply Nat.dvd_antisymm
  · simpa only [transform_inv_transform] using content_dvd_transform g⁻¹ (transform g Q)
  · exact content_dvd_transform g Q

/-- Evaluation of an integral binary quadratic form. -/
def evaluate (Q : BinaryQuadraticForm) (u v : ℤ) : ℤ :=
  Q.a * u ^ 2 + Q.b * u * v + Q.c * v ^ 2

/-- Completing the square without introducing fractions. -/
theorem four_mul_a_evaluate (Q : BinaryQuadraticForm) (u v : ℤ) :
    4 * Q.a * Q.evaluate u v = (2 * Q.a * u + Q.b * v) ^ 2 - Q.discriminant * v ^ 2 := by
  simp only [evaluate, discriminant]
  ring

theorem evaluate_pos (Q : BinaryQuadraticForm) (ha : 0 < Q.a)
    (hD : Q.discriminant < 0) (u v : ℤ) (huv : u ≠ 0 ∨ v ≠ 0) :
    0 < Q.evaluate u v := by
  by_cases hv : v = 0
  · subst v
    have hu : u ≠ 0 := by simpa using huv
    simpa [evaluate] using mul_pos ha (sq_pos_of_ne_zero hu)
  · have hp : 0 < 4 * Q.a * Q.evaluate u v := by
      rw [four_mul_a_evaluate, sub_eq_add_neg, ← neg_mul]
      exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos (neg_pos.mpr hD) (sq_pos_of_ne_zero hv))
    exact pos_of_mul_pos_left (by simpa only [mul_comm] using hp)
      (le_of_lt (mul_pos (by norm_num : (0 : ℤ) < 4) ha))

theorem pullback_a_pos (Q : BinaryQuadraticForm) (ha : 0 < Q.a)
    (hD : Q.discriminant < 0) (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det = 1) :
    0 < (Q.pullback M).a := by
  apply Q.evaluate_pos ha hD (M 0 0) (M 1 0)
  by_cases h : M 0 0 = 0
  · right
    intro h'
    simp [Matrix.det_fin_two, h, h'] at hM
  · exact Or.inl h

end SptClassification.BinaryQuadraticForm
