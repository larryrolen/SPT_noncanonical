/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PositiveCuspAction

/-!
# Products in determinant-normalized cusp charts

The classical even-weight slash respects products and natural powers.
The final formula separates a weight-zero pole-clearing factor from the
positive-weight factors used to clear the CM lift.
-/

public section

namespace SptClassification.PositiveCuspAction

open UpperHalfPlane
open scoped MatrixGroups

/-- Classical slash weights add under pointwise multiplication. -/
theorem evenWeightSlash_mul (m n : ℕ) (g : GL (Fin 2) ℝ)
    (f h : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    evenWeightSlash (m + n) g (fun w => f w * h w) z =
      evenWeightSlash m g f z * evenWeightSlash n g h z := by
  simp only [evenWeightSlash_apply, Nat.mul_add, pow_add]
  ring

/-- Taking a natural power multiplies the classical slash weight. -/
theorem evenWeightSlash_pow (m n : ℕ) (g : GL (Fin 2) ℝ)
    (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    evenWeightSlash (m * n) g (fun w => f w ^ n) z =
      evenWeightSlash m g f z ^ n := by
  simp only [evenWeightSlash_apply, mul_pow, div_pow, ← pow_mul, Nat.mul_assoc]

/-- A weight-zero factor is evaluated at the chart point; the remaining
factors retain their separate determinant normalizations. -/
theorem evenWeightSlash_clearing (m n r : ℕ) (g : GL (Fin 2) ℝ)
    (f P J : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    evenWeightSlash (m * r + n) g (fun w => f w ^ r * (P w * J w)) z =
      P (g • z) * evenWeightSlash m g f z ^ r *
        evenWeightSlash n g J z := by
  rw [evenWeightSlash_mul, evenWeightSlash_pow]
  have hP : evenWeightSlash n g (fun w => P w * J w) z =
      P (g • z) * evenWeightSlash n g J z := by
    simp only [evenWeightSlash_apply]
    ring
  rw [hP]
  ring

end SptClassification.PositiveCuspAction
