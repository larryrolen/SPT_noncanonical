/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PositiveCuspAction

/-!
# Explicit positive determinant cusp matrices

Real matrix entries give an element of `GL₂(ℝ)` and its actual actions on the
upper half-plane and the real cusps. These formulas connect classical cusp
coordinates with the slash and boundedness APIs.
-/

public section

namespace SptClassification.PositiveCuspAction

open Matrix UpperHalfPlane OnePoint
open scoped MatrixGroups

/-- An explicit real matrix with positive determinant, as a group element. -/
noncomputable def positiveMatrix (a b c d : ℝ) (h : 0 < a * d - b * c) :
    GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d]
    (by simpa [Matrix.det_fin_two] using h.ne')

@[simp] theorem positiveMatrix_val (a b c d : ℝ) (h : 0 < a * d - b * c) :
    (positiveMatrix a b c d h : Matrix (Fin 2) (Fin 2) ℝ) = !![a, b; c, d] := by
  exact Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

@[simp] theorem positiveMatrix_det (a b c d : ℝ) (h : 0 < a * d - b * c) :
    (positiveMatrix a b c d h).det.val = a * d - b * c := by
  change Matrix.det (positiveMatrix a b c d h : Matrix (Fin 2) (Fin 2) ℝ) = _
  rw [positiveMatrix_val]
  simp [Matrix.det_fin_two]

@[simp] theorem positiveMatrix_denom (a b c d : ℝ) (h : 0 < a * d - b * c)
    (z : UpperHalfPlane) :
    denom (positiveMatrix a b c d h) z = (c : ℂ) * z + d := by
  simp [denom, positiveMatrix]

/-- Positive determinant gives the usual fractional-linear formula. -/
theorem positiveMatrix_smul (a b c d : ℝ) (h : 0 < a * d - b * c)
    (z : UpperHalfPlane) :
    ((positiveMatrix a b c d h) • z : UpperHalfPlane) =
      ((a : ℂ) * z + b) / ((c : ℂ) * z + d) := by
  have hg : 0 < (positiveMatrix a b c d h).det.val := by simpa using h
  rw [UpperHalfPlane.coe_smul_of_det_pos hg]
  simp [UpperHalfPlane.num, denom, positiveMatrix]

/-- The chart takes infinity to the ratio of its first-column entries. -/
theorem positiveMatrix_smul_infty (a b c d : ℝ) (h : 0 < a * d - b * c)
    (hc : c ≠ 0) :
    positiveMatrix a b c d h • (∞ : OnePoint ℝ) = (↑(a / c) : OnePoint ℝ) := by
  rw [OnePoint.smul_infty_eq_ite]
  simp [positiveMatrix, hc]

end SptClassification.PositiveCuspAction
