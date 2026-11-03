/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMRationalAction
import Mathlib.Tactic.FieldSimp

/-!
# The actual CM action is not integer multiplication

The positive imaginary part of the chosen quadratic generator distinguishes
its action on the complex torus from every integer scalar. Transport through
the constructed uniformization gives the same statement in the rational
endomorphism ring. This supplies the nontrivial-CM hypothesis for algebraic
descent; no algebraicity or specialization theorem is assumed here.
-/

public section

namespace SptClassification

namespace LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- If the CM action were scalar, surjectivity of multiplication by the
nonzero complex number `α-m` would kill every torus point, including `[1/6]`. -/
theorem torusGenerator_not_integer (hodd : Q.b % 2 = 1) (m : ℤ) :
    ¬ (∀ x : Q.ComplexTorus, Q.torusGenerator hodd x = m • x) := by
  intro h
  have hne : cmGenerator D - (m : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (cmGenerator_ne_intCast D m)
  let z : ℂ := (1 / 6) / (cmGenerator D - (m : ℂ))
  have hz := h (Q.torusPoint z)
  rw [Q.torusGenerator_point, ← map_zsmul] at hz
  have hzero : Q.torusPoint (cmGenerator D * z - m • z) = 0 := by
    rw [map_sub, hz, sub_self]
  have heq : cmGenerator D * z - m • z = (1 / 6 : ℂ) := by
    rw [zsmul_eq_mul]
    dsimp [z]
    field_simp
    <;> ring
  rw [heq, ← Q.torusSixPoint_eq] at hzero
  have hdiv := (Q.torusSixPoint_nsmul_eq_zero 1).mp (by simpa using hzero)
  norm_num at hdiv

/-- The uniformized CM action is not integer multiplication on curve points. -/
theorem curveGenerator_not_integer (hodd : Q.b % 2 = 1) (m : ℤ) :
    ¬ (∀ x : Q.complexCurve.toAffine.Point, Q.curveGenerator hodd x = m • x) := by
  intro h
  apply Q.torusGenerator_not_integer hodd m
  intro x
  apply Q.curveUniformization.injective
  simpa only [Q.curveGenerator_uniformization, map_zsmul] using
    h (Q.curveUniformization x)

/-- Nontrivial complex multiplication in the actual rational endomorphism ring. -/
theorem rationalGenerator_ne_intCast (hodd : Q.b % 2 = 1) (m : ℤ) :
    Q.rationalGenerator hodd ≠
      (m : RationalPointMap.endomorphismRing Q.complexCurve) := by
  classical
  intro h
  apply Q.curveGenerator_not_integer hodd m
  intro x
  rw [← Q.rationalGenerator_action, h, map_intCast]
  exact AddMonoid.End.intCast_apply m x

end LevelSixForm
end SptClassification
