/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixModuliCoordinate
import Mathlib.Tactic.LinearCombination

/-!
# The marked Tate parameter from short Weierstrass coordinates

For a marked point `(x,y)` on `y² = x³ + a₄*x + a₆`, its tangent slope
determines its Tate parameter. This calculation retains the marked point;
unlike the j-invariant it distinguishes the cyclic subgroup.
-/

public section

namespace SptClassification.LevelSixWeierstrass

variable {F : Type*} [Field F] [CharZero F]

/-- The parameter calculated from the marked point and its tangent slope. -/
def shortTateParameter (a₄ x y : F) : F :=
  let s := (3 * x ^ 2 + a₄) / (2 * y)
  1 - s * (3 * x - s ^ 2) / y

theorem shortTateParameter_eq (a₄ x y : F) :
    shortTateParameter a₄ x y =
      1 - ((3 * x ^ 2 + a₄) / (2 * y)) *
        (3 * x - ((3 * x ^ 2 + a₄) / (2 * y)) ^ 2) / y := (rfl)

/-- Coefficient comparison determines the parameter of every pointed Tate
normalization of a short equation. The coordinate convention is that `C`
sends the Tate origin to `(C.r,C.t)` on the short equation. -/
theorem shortTateParameter_eq_of_variableChange
    (W : WeierstrassCurve F) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0)
    (c : F) (C : WeierstrassCurve.VariableChange F)
    (hC : C • W = tateCurve c) (hy : C.t ≠ 0) :
    shortTateParameter W.a₄ C.r C.t = c := by
  have ha₁ := congrArg WeierstrassCurve.a₁ hC
  have ha₂ := congrArg WeierstrassCurve.a₂ hC
  have ha₃ := congrArg WeierstrassCurve.a₃ hC
  have ha₄ := congrArg WeierstrassCurve.a₄ hC
  simp only [WeierstrassCurve.variableChange_a₁, h₁, tateCurve_a₁] at ha₁
  simp only [WeierstrassCurve.variableChange_a₂, h₁, h₂, tateCurve_a₂] at ha₂
  simp only [WeierstrassCurve.variableChange_a₃, h₁, h₃, tateCurve_a₃] at ha₃
  simp only [WeierstrassCurve.variableChange_a₄, h₁, h₂, h₃, tateCurve_a₄] at ha₄
  simp only [Units.val_inv_eq_inv_val] at ha₁ ha₂ ha₃ ha₄
  have hs : (3 * C.r ^ 2 + W.a₄) / (2 * C.t) = C.s := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hy)).mpr
    field_simp at ha₄
    linear_combination ha₄
  have hscale : (C.u : F) * (3 * C.r - C.s ^ 2) = 2 * C.t := by
    field_simp at ha₂ ha₃
    linear_combination (C.u : F) * ha₂ - ha₃
  have hlin : 2 * C.s = (1 - c) * (C.u : F) := by
    field_simp at ha₁
    linear_combination ha₁
  unfold shortTateParameter
  rw [hs]
  field_simp
  linear_combination -(3 * C.r - C.s ^ 2) / 2 * hlin - (1 - c) / 2 * hscale

/-- The point in a nonsingular Tate normalization of a short equation has
nonzero y-coordinate. This avoids a separate torsion computation. -/
theorem variableChange_t_ne_zero (W : WeierstrassCurve F)
    (h₁ : W.a₁ = 0) (h₃ : W.a₃ = 0) (c : F)
    (hc : (tateCurve c).Δ ≠ 0) (C : WeierstrassCurve.VariableChange F)
    (hC : C • W = tateCurve c) : C.t ≠ 0 := by
  intro ht
  have ha₃ := congrArg WeierstrassCurve.a₃ hC
  simp only [WeierstrassCurve.variableChange_a₃, h₁, h₃, ht,
    tateCurve_a₃, mul_zero, zero_add, add_zero] at ha₃
  have hz : c = 0 ∨ c + 1 = 0 := by
    simpa only [mul_eq_zero, neg_eq_zero] using ha₃.symm
  rw [tateCurve_discriminant] at hc
  rcases hz with h | h
  · simp [h] at hc
  · simp [h] at hc

end SptClassification.LevelSixWeierstrass

namespace SptClassification.LevelSixPair

open LevelSixWeierstrass

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F] [IsAlgClosed F]

/-- Evaluate the abstract marked coordinate from the actual short-equation
point. Only the existing pointed Tate normalization and isomorphism
classification are used; there is no new literature admission. -/
theorem tateCoordinate_eq_shortTateParameter (A : LevelSixPair F)
    (h₁ : A.curve.a₁ = 0) (h₂ : A.curve.a₂ = 0) (h₃ : A.curve.a₃ = 0)
    (x y : F) (hxy : A.curve.toAffine.Nonsingular x y)
    (hP : A.point = .some x y hxy) :
    y ≠ 0 ∧ tateCoordinate (by norm_num) A = shortTateParameter A.curve.a₄ x y := by
  obtain ⟨hc, hO, e, he⟩ := tateCoordinate_spec (by norm_num) A
  obtain ⟨C, hC, hf⟩ := RationalPointMap.exists_variableChange_of_curveEquiv
    _ _ ⟨isUnit_iff_ne_zero.mpr hc⟩ A.elliptic e.symm
  obtain ⟨hO', hf⟩ := hf 0 0 hO
  have he' : e.toAddEquiv.symm (.some 0 0 hO) = A.point :=
    e.toAddEquiv.symm_apply_eq.mpr he.symm
  rw [RationalPointMap.CurveEquiv.symm_toAddEquiv, he', hP,
    WeierstrassCurve.Affine.Point.some.injEq] at hf
  have hr : C.r = x := by simpa using hf.1.symm
  have ht : C.t = y := by simpa using hf.2.symm
  have hy := variableChange_t_ne_zero A.curve h₁ h₃ _ hc C hC
  refine ⟨ht ▸ hy, ?_⟩
  have h := shortTateParameter_eq_of_variableChange A.curve h₁ h₂ h₃ _ C hC hy
  simpa only [hr, ht] using h.symm

end SptClassification.LevelSixPair
