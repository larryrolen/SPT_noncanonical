/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixTateCoordinates
public import SptClassification.QuadraticForms.LevelSixPoint
public import SptClassification.QuadraticForms.LevelSixPointedIsomorphism
public import SptClassification.QuadraticForms.VariableChangeIsomorphism
import Mathlib.Tactic.NormNum

/-!
# Marked Tate models of cyclic-six pairs

The standard Tate normal form is a named literature input. Clearing its
parameter denominators gives an actual pointed isomorphism to the integral
family. This constructs a marked model, without identifying its parameter
with the analytic eta quotient or asserting specialization of CM actions.
-/

public section

namespace SptClassification

namespace LevelSixPair

/-- The order-six case of the marked Tate normal form [sutherland2012,
§2, p. 3; Proposition 1, p. 4; Table 4, p. 14, arXiv:0811.0296v4].
The normal form is `y² + (1-c)xy - b*y = x³ - b*x²`, with the given point
sent to `(0,0)`. In the source's parameters, `F₆(r,s) = s-1`,
`c = s*(r-1)`, and `b = r*s*(r-1)`, so `b = c*(c+1)`.
Nonsingularity is retained. We restrict to algebraically closed fields away
from characteristics two and three to match the rational point-map API.
This is a literature admission about arbitrary marked elliptic curves;
it contains no CM, eta, or reduction assertion. -/
theorem exists_tate_model
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (A : LevelSixPair F) (h6 : (6 : F) ≠ 0) :
    ∃ (c : F) (_ : (LevelSixWeierstrass.tateCurve c).Δ ≠ 0)
      (hO : (LevelSixWeierstrass.tateCurve c).toAffine.Nonsingular 0 0)
      (e : RationalPointMap.CurveEquiv A.curve (LevelSixWeierstrass.tateCurve c)),
      e.toAddEquiv A.point = .some 0 0 hO := by
  sorry

end LevelSixPair

namespace LevelSixWeierstrass

variable {F : Type*} [Field F]

/-- The integral-family parameter obtained from a nonsingular Tate model. -/
def integralParameter (c : F) : F := -72 * c / (9 * c + 1)

theorem integralParameter_eq (c : F) : integralParameter c = -72 * c / (9 * c + 1) :=
  (rfl)

/-- This parameter change is defined on every nonsingular Tate fiber away
from characteristics two and three, and misses the three singular fibers. -/
theorem integralParameter_regular (c : F) (h6 : (6 : F) ≠ 0)
    (hΔ : (tateCurve c).Δ ≠ 0) :
    (curve (integralParameter c)).Δ ≠ 0 ∧
      tateParameter (integralParameter c) = c := by
  have h23 : (2 : F) * 3 ≠ 0 := by norm_num; exact h6
  have h2 := (mul_ne_zero_iff.mp h23).1
  have h3 := (mul_ne_zero_iff.mp h23).2
  have h8 : (8 : F) ≠ 0 := by
    convert pow_ne_zero 3 h2 using 1 <;> norm_num
  have h9 : (9 : F) ≠ 0 := by
    convert pow_ne_zero 2 h3 using 1 <;> norm_num
  have h72 : (72 : F) ≠ 0 := by
    convert mul_ne_zero h8 h9 using 1 <;> norm_num
  rw [tateCurve_discriminant] at hΔ
  have hd : 9 * c + 1 ≠ 0 := (mul_ne_zero_iff.mp hΔ).2
  have hc : c ≠ 0 := by
    intro h; simp [h] at hΔ
  have hc1 : c + 1 ≠ 0 := by
    intro h; simp [h] at hΔ
  have he8 : integralParameter c + 8 = 8 / (9 * c + 1) := by
    unfold integralParameter
    apply (eq_div_iff hd).mpr
    rw [add_mul, div_mul_cancel₀ _ hd]
    ring
  have he9 : integralParameter c + 9 = 9 * (c + 1) / (9 * c + 1) := by
    unfold integralParameter
    apply (eq_div_iff hd).mpr
    rw [add_mul, div_mul_cancel₀ _ hd]
    ring
  have ht : integralParameter c ≠ 0 :=
    div_ne_zero (mul_ne_zero (neg_ne_zero.mpr h72) hc) hd
  have ht8 : integralParameter c + 8 ≠ 0 := by
    rw [he8]; exact div_ne_zero h8 hd
  have ht9 : integralParameter c + 9 ≠ 0 := by
    rw [he9]; exact div_ne_zero (mul_ne_zero h9 hc1) hd
  constructor
  · intro hzero
    rcases (discriminant_eq_zero_iff (integralParameter c) h6).mp hzero with h | h | h
    · exact ht h
    · exact ht8 (by rw [h]; ring)
    · exact ht9 (by rw [h]; ring)
  · rw [tateParameter_eq]
    rw [he8]
    apply (div_eq_iff (mul_ne_zero h9 (div_ne_zero h8 hd))).mpr
    unfold integralParameter
    ring

variable [DecidableEq F] [IsAlgClosed F]

/-- An actual pointed rational isomorphism between nonsingular Tate models
preserves the parameter. The geometric isomorphism theorem reduces the claim
to the previously proved coefficient comparison. -/
theorem tateParameter_eq_of_pointed_equiv (c d : F)
    (hc : (tateCurve c).Δ ≠ 0) (hd : (tateCurve d).Δ ≠ 0)
    (hO : (tateCurve c).toAffine.Nonsingular 0 0)
    (hO' : (tateCurve d).toAffine.Nonsingular 0 0)
    (e : RationalPointMap.CurveEquiv (tateCurve c) (tateCurve d))
    (he : e.toAddEquiv (.some 0 0 hO) = .some 0 0 hO') : c = d := by
  obtain ⟨C, hC, hformula⟩ := RationalPointMap.exists_variableChange_of_curveEquiv
    (tateCurve c) (tateCurve d) ⟨isUnit_iff_ne_zero.mpr hc⟩
    ⟨isUnit_iff_ne_zero.mpr hd⟩ e
  obtain ⟨hO'', hformula⟩ := hformula 0 0 hO
  rw [he, WeierstrassCurve.Affine.Point.some.injEq] at hformula
  have hr : C.r = 0 := by simpa using hformula.1.symm
  have ht : C.t = 0 := by simpa using hformula.2.symm
  exact (tateParameter_eq_of_variableChange d c hd C hC hr ht).symm

/-- Every marked cyclic-six pair has a pointed model in the integral family.
The parameter is supplied by Tate normalization; equality with the actual
eta value is a separate analytic statement. -/
theorem exists_integral_model (A : LevelSixPair F) (h6 : (6 : F) ≠ 0) :
    ∃ (t : F) (hΔ : (curve t).Δ ≠ 0)
      (e : RationalPointMap.CurveEquiv A.curve (curve t)),
      e.toAddEquiv A.point = sixPoint t hΔ := by
  obtain ⟨c, hc, hO, e, he⟩ := A.exists_tate_model h6
  obtain ⟨hΔ, hparam⟩ := integralParameter_regular c h6 hc
  have h23 : (2 : F) * 3 ≠ 0 := by norm_num; exact h6
  have h9 : (9 : F) ≠ 0 := by
    convert pow_ne_zero 2 (mul_ne_zero_iff.mp h23).2 using 1 <;> norm_num
  have ht8 := (parameter_ne_zero _ hΔ).2.1
  have hC : tateChange (integralParameter c) h9 ht8 • tateCurve c =
      curve (integralParameter c) := by
    simpa only [hparam] using tateChange_curve (integralParameter c) h9 ht8
  have hEc : (tateCurve c).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hc⟩
  have hEt : (curve (integralParameter c)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  obtain ⟨f, hf⟩ := RationalPointMap.exists_curveEquiv_of_variableChange
    (curve (integralParameter c)) (tateCurve c) hEc _ hC
  obtain ⟨hO', hfO⟩ := hf 0 0 (origin_nonsingular _ hΔ)
  have hfP : f.toAddEquiv (sixPoint (integralParameter c) hΔ) = .some 0 0 hO := by
    simpa [sixPoint_eq] using hfO
  refine ⟨integralParameter c, hΔ, e.trans f.symm A.elliptic hEc hEt, ?_⟩
  rw [RationalPointMap.CurveEquiv.trans_apply, he]
  apply f.toAddEquiv.injective
  simpa only [RationalPointMap.CurveEquiv.symm_toAddEquiv,
    f.toAddEquiv.apply_symm_apply] using hfP.symm

end LevelSixWeierstrass
end SptClassification
