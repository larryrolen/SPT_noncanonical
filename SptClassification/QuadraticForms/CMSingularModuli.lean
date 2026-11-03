/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMMarkedField

/-!
# Singular moduli and the finite marked CM field

The classical singular-moduli theorem applies to a complex lattice admitting
a noninteger multiplier. The manuscript's multiplier and its preservation of
the actual period lattice are already constructed. Its application removes
the j-algebraicity hypothesis from finiteness of the marked field.
-/

public section

namespace SptClassification

namespace ComplexUniformization

/-- Singular moduli [silverman1994, Chapter II, Theorem 6.1], in lattice form.
Multiplication by `a` preserves the lattice and is not integer multiplication,
so the complex elliptic curve has CM. The theorem covers arbitrary CM orders;
no maximal-order hypothesis is imposed. The invariant is the usual `j`, with
the factor 1728, of `y² = x³ - g₂*x/4 - g₃/4`.

The indexed informal theorem states that every complex CM elliptic curve has
algebraic-integral j. Its link to the book locator is corroborated by an
indexed citation; the primary book copy has not been independently inspected.
This is a visible literature admission, not a specialization assertion. -/
theorem latticeCM_j_isIntegral (L : PeriodPair) (a : ℂ)
    (ha : ∀ z ∈ L.lattice, a * z ∈ L.lattice)
    (hne : ∀ m : ℤ, a ≠ (m : ℂ)) :
    letI := curve_isElliptic L
    IsIntegral ℤ (curve L).j := by
  sorry

end ComplexUniformization

namespace LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The actual lattice invariant is a singular modulus. The input multiplier
is `(1 + sqrt D)/2` and the preserved lattice is exactly `ℤ + ℤτ_Q`. -/
theorem complexCurve_j_isIntegral (hodd : Q.b % 2 = 1) :
    letI := Q.complexCurve_isElliptic
    IsIntegral ℤ Q.complexCurve.j := by
  apply ComplexUniformization.latticeCM_j_isIntegral Q.periodPair (cmGenerator D)
  · intro z hz
    have hz' : z ∈ Q.periodLattice := by
      change z ∈ Q.periodPair.lattice.toAddSubgroup at hz
      simpa only [Q.periodPair_lattice] using hz
    have hmul := Q.complexGeneratorMap_preserves hodd z hz'
    rw [complexGeneratorMap_apply] at hmul
    change cmGenerator D * z ∈ Q.periodPair.lattice.toAddSubgroup
    simpa only [Q.periodPair_lattice] using hmul
  · exact cmGenerator_ne_intCast D

/-- Algebraicity of the actual j-value over `ℚ`, derived from singular-moduli
integrality rather than assumed as a parameter. -/
theorem complexCurve_j_isAlgebraic (hodd : Q.b % 2 = 1) :
    letI := Q.complexCurve_isElliptic
    IsAlgebraic ℚ Q.complexCurve.j := by
  letI := Q.complexCurve_isElliptic
  exact ((Q.complexCurve_j_isIntegral hodd).tower_top (A := ℚ)).isAlgebraic

/-- The previously constructed field containing the actual order-six marking
is a finite extension of `ℚ`. CM-action descent and good reduction are separate. -/
theorem markedField_finiteDimensional_of_cm (hodd : Q.b % 2 = 1) :
    FiniteDimensional ℚ Q.markedField :=
  Q.markedField_finiteDimensional_rat (Q.complexCurve_j_isAlgebraic hodd)

end LevelSixForm

end SptClassification
