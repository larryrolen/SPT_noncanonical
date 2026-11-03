/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.ShortTateParameter
public import SptClassification.QuadraticForms.CMMarkedModel

/-!
# The marked CM coordinate in Weierstrass functions

The Tate coordinate of the original CM pair is evaluated at the actual
point `1/6` on its complex torus. Its identification with the eta quotient
is a separate analytic identity; no such identity is assumed here.
-/

public section

namespace SptClassification.LevelSixForm

open LevelSixWeierstrass

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The chosen level-six generator is not a period. -/
theorem one_sixth_not_mem_periodLattice : (1 / 6 : ℂ) ∉ Q.periodLattice := by
  intro h
  have hz : Q.torusSixPoint = 0 := by
    rw [Q.torusSixPoint_eq, Q.torusPoint_eq_zero]
    exact h
  have horder := (Q.torusSixPoint_nsmul_eq_zero 1).mp (by simp [hz])
  norm_num at horder

/-- The point used for the CM marking has precisely the standard
Weierstrass-function coordinates at `1/6`. -/
theorem curveSixPoint_coordinates :
    ∃ h : Q.complexCurve.toAffine.Nonsingular
        (Q.periodPair.weierstrassP (1 / 6))
        (Q.periodPair.derivWeierstrassP (1 / 6) / 2),
      Q.curveSixPoint = .some (Q.periodPair.weierstrassP (1 / 6))
        (Q.periodPair.derivWeierstrassP (1 / 6) / 2) h := by
  simpa only [Q.curveSixPoint_eq, Q.torusSixPoint_eq] using
    Q.curveUniformization_coordinates (1 / 6) Q.one_sixth_not_mem_periodLattice

/-- Evaluation of the marked coordinate on the original lattice cubic.
The tangent slope is `(3*wp(1/6)^2-g₂/4)/wp'(1/6)` in the normalization
`y=wp'/2`. This deduction retains the subgroup, unlike equality of j. -/
theorem complexPair_tateCoordinate_eq :
    Q.periodPair.derivWeierstrassP (1 / 6) / 2 ≠ 0 ∧
      LevelSixPair.tateCoordinate (by norm_num) Q.complexPair =
        shortTateParameter (-Q.periodPair.g₂ / 4)
          (Q.periodPair.weierstrassP (1 / 6))
          (Q.periodPair.derivWeierstrassP (1 / 6) / 2) := by
  obtain ⟨h, hP⟩ := Q.curveSixPoint_coordinates
  have h₁ : Q.complexPair.curve.a₁ = 0 := by
    rw [Q.complexPair_curve]; exact ComplexUniformization.curve_a₁ _
  have h₂ : Q.complexPair.curve.a₂ = 0 := by
    rw [Q.complexPair_curve]; exact ComplexUniformization.curve_a₂ _
  have h₃ : Q.complexPair.curve.a₃ = 0 := by
    rw [Q.complexPair_curve]; exact ComplexUniformization.curve_a₃ _
  have h' : Q.complexPair.curve.toAffine.Nonsingular
      (Q.periodPair.weierstrassP (1 / 6))
      (Q.periodPair.derivWeierstrassP (1 / 6) / 2) := by
    simpa only [Q.complexPair_curve] using h
  have hP' : Q.complexPair.point = .some _ _ h' := by
    simpa only [complexPair] using hP
  simpa only [Q.complexPair_curve, ComplexUniformization.curve_a₄] using
    Q.complexPair.tateCoordinate_eq_shortTateParameter h₁ h₂ h₃ _ _ h' hP'

end SptClassification.LevelSixForm
