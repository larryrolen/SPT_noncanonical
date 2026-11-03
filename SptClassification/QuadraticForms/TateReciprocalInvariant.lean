/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.TateCuspBranch
public import SptClassification.QuadraticForms.ShortTateParameter
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Reciprocal invariants of marked Tate coordinates

Admissible coordinate changes preserve the rational reciprocal invariant,
including its field-division value at c₄ = 0. This connects the marked Tate
coordinate to the invariant of its original curve.
-/

public section

namespace SptClassification

namespace RationalPointMap

/-- The reciprocal invariant equals the field inverse of j, also when j is zero. -/
theorem reciprocalInvariant_eq_inv_j {F : Type*} [Field F]
    (W : WeierstrassCurve F) [W.IsElliptic] :
    W.Δ / W.c₄ ^ 3 = W.j⁻¹ := by
  simp [WeierstrassCurve.j_eq, div_eq_mul_inv, mul_comm]

/-- The weights twelve and four cancel in the reciprocal invariant. -/
theorem reciprocalInvariant_variableChange {F : Type*} [Field F]
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) :
    (C • W).Δ / (C • W).c₄ ^ 3 = W.Δ / W.c₄ ^ 3 := by
  rw [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.variableChange_c₄,
    mul_pow, ← pow_mul]
  norm_num only
  exact mul_div_mul_left _ _ (pow_ne_zero _ (Units.ne_zero _))

/-- Rational pointed equivalences preserve the reciprocal invariant. -/
theorem CurveEquiv.reciprocalInvariant_eq {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    {W W' : WeierstrassCurve F} (e : CurveEquiv W W')
    (hW : W.IsElliptic) (hW' : W'.IsElliptic) :
    W.Δ / W.c₄ ^ 3 = W'.Δ / W'.c₄ ^ 3 := by
  obtain ⟨C, hC, _⟩ := exists_variableChange_of_curveEquiv W W' hW hW' e
  rw [← hC]
  exact reciprocalInvariant_variableChange W' C

end RationalPointMap

namespace LevelSixPair

/-- The chosen marked Tate coordinate has the invariant of its original curve. -/
theorem tateCoordinate_reciprocalInvariant (A : LevelSixPair ℂ) :
    LevelSixWeierstrass.tateReciprocalInvariant (tateCoordinate (by norm_num) A) =
      A.curve.Δ / A.curve.c₄ ^ 3 := by
  obtain ⟨hc, _, e, _⟩ := tateCoordinate_spec (by norm_num) A
  rw [LevelSixWeierstrass.tateReciprocalInvariant_eq]
  exact (e.reciprocalInvariant_eq A.elliptic ⟨isUnit_iff_ne_zero.mpr hc⟩).symm

end LevelSixPair

namespace LevelSixWeierstrass

/-- The explicit integral-to-Tate change also preserves the reciprocal invariant. -/
theorem tateParameter_reciprocalInvariant (t : ℂ) (h8 : t + 8 ≠ 0) :
    tateReciprocalInvariant (tateParameter t) = (curve t).Δ / (curve t).c₄ ^ 3 := by
  rw [tateReciprocalInvariant_eq, ← tateChange_curve t (by norm_num) h8]
  exact (RationalPointMap.reciprocalInvariant_variableChange _ _).symm

end LevelSixWeierstrass
end SptClassification
