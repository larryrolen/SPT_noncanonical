/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMUniformization
public import SptClassification.QuadraticForms.RationalEndomorphisms

/-!
# Rationality of the actual complex CM action

The classical input concerns multiplication between arbitrary complex lattices.
It certifies rational coordinates for the same additive point map whose action
on the level-six subgroup was constructed in `CMUniformization`. It asserts
neither descent to a number field nor good-reduction specialization.
-/

public section

namespace SptClassification.ComplexUniformization

/-- Rationality of lattice multiplication under Weierstrass uniformization
[silverman2009, Chapter VI, §3, generation of the elliptic function field by
`℘, ℘'`; §4, maps between complex tori]. The coordinate normalization here is
`(℘, ℘'/2)` on `y² = x³ - g₂*x/4 - g₃/4`.

For `a ≠ 0`, the functions `℘(a*z)` and `℘'(a*z)/2` are elliptic for the
source lattice and hence rational in its Weierstrass coordinates; their poles
give only finitely many exceptional points on the torus. For `a = 0` the
point map is zero. This is a named literature admission. The section locators
are retained without claiming a verified primary-source theorem number.
The point-action compatibility hypothesis is essential. -/
theorem latticeMultiplication_isRational (L L' : PeriodPair) (a : ℂ)
    (ha : ∀ z ∈ L.lattice, a * z ∈ L'.lattice)
    (f : (curve L).toAffine.Point →+ (curve L').toAffine.Point)
    (hf : ∀ z : ℂ,
      f (uniformization L (QuotientAddGroup.mk' L.lattice.toAddSubgroup z)) =
        uniformization L' (QuotientAddGroup.mk' L'.lattice.toAddSubgroup (a * z))) :
    RationalPointMap.IsRational f := by
  sorry

end ComplexUniformization

namespace LevelSixForm

variable {D : ℤ} {r : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D r)

/-- The already constructed CM action on the actual complex cubic has
compatible rational coordinate representatives. Its subgroup action is
unchanged; only the general lattice-rationality theorem is admitted. -/
theorem curveGenerator_isRational (hodd : Q.b % 2 = 1) :
    RationalPointMap.IsRational (Q.curveGenerator hodd) := by
  refine ComplexUniformization.latticeMultiplication_isRational
    Q.periodPair Q.periodPair (cmGenerator D) ?_ (Q.curveGenerator hodd) ?_
  · intro z hz
    have hz' : z ∈ Q.periodLattice := by
      change z ∈ Q.periodPair.lattice.toAddSubgroup at hz
      simpa only [Q.periodPair_lattice] using hz
    have hmul := Q.complexGeneratorMap_preserves hodd z hz'
    rw [complexGeneratorMap_apply] at hmul
    change cmGenerator D * z ∈ Q.periodPair.lattice.toAddSubgroup
    simpa only [Q.periodPair_lattice] using hmul
  · intro z
    rw [← Q.curveUniformization_torusPoint, ← Q.curveUniformization_torusPoint,
      Q.curveGenerator_uniformization, Q.torusGenerator_point]

/-- The CM generator as a rational endomorphism of the actual cubic. -/
noncomputable def rationalGenerator (hodd : Q.b % 2 = 1) :
    RationalPointMap.endomorphismRing Q.complexCurve :=
  RationalPointMap.ofRational (Q.curveGenerator hodd) (Q.curveGenerator_isRational hodd)

theorem rationalGenerator_action (hodd : Q.b % 2 = 1) :
    RationalPointMap.pointAction Q.complexCurve (Q.rationalGenerator hodd) =
      Q.curveGenerator hodd := by
  unfold rationalGenerator
  exact RationalPointMap.pointAction_ofRational _ _

/-- The manuscript's quadratic relation now holds in the rational
endomorphism ring, with multiplication given by composition of actual maps. -/
theorem rationalGenerator_quadratic (hodd : Q.b % 2 = 1) (n : ℕ)
    (hn : 4 * (n : ℤ) = 1 - D) :
    Q.rationalGenerator hodd * Q.rationalGenerator hodd - Q.rationalGenerator hodd +
      (n : RationalPointMap.endomorphismRing Q.complexCurve) = 0 := by
  apply RationalPointMap.pointAction_injective Q.complexCurve
  simp only [map_add, map_sub, map_mul, map_natCast, map_zero,
    Q.rationalGenerator_action]
  apply AddMonoidHom.ext
  intro x
  exact Q.curveGenerator_quadratic hodd n hn x

/-- The same rational endomorphism acts on the distinguished order-six point
by the orientation scalar of the binary quadratic form. -/
theorem rationalGenerator_sixPoint (hodd : Q.b % 2 = 1) :
    RationalPointMap.pointAction Q.complexCurve (Q.rationalGenerator hodd) Q.curveSixPoint =
      ((Q.b + 1) / 2 : ℤ) • Q.curveSixPoint := by
  rw [Q.rationalGenerator_action]
  exact Q.curveGenerator_sixPoint hodd

end LevelSixForm
end SptClassification
