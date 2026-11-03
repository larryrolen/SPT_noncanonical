/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMRationalSpecialization
public import SptClassification.QuadraticForms.RationalCurveIsomorphism

/-!
# CM separation on isomorphic reduced pairs

Equality of moduli points supplies an isomorphism of marked elliptic curves,
not equality of chosen equations. The theorem below transports the second
specialized action along a rational isomorphism and proves the orientation
contradiction on the first curve. Existence of good reduction and the marked
isomorphism are separate geometric inputs.
-/

public section

namespace SptClassification.LevelSixForm

/-- Two independently specialized CM actions on isomorphic marked curves
cannot commute after transport. The common-image hypothesis involves the
actual subgroup images, and the curve isomorphism uses compatible rational
coordinates in both directions. There is no splitting restriction. -/
theorem rational_specializations_not_commute_of_pair_iso
    {D : ℤ} {r s : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) (R : LevelSixForm D s)
    (hQ : Q.b % 2 = 1) (hR : R.b % 2 = 1)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 - D)
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W₁ W₂ : WeierstrassCurve F) (hW₁ : W₁.IsElliptic) (hW₂ : W₂.IsElliptic)
    (σQ : RationalPointMap.endomorphismRing Q.complexCurve →+*
      RationalPointMap.endomorphismRing W₁)
    (σR : RationalPointMap.endomorphismRing R.complexCurve →+*
      RationalPointMap.endomorphismRing W₂)
    (eQ : Q.curveLevelSix →+ W₁.toAffine.Point)
    (eR : R.curveLevelSix →+ W₂.toAffine.Point)
    (heQ : Function.Injective eQ)
    (φ : RationalPointMap.CurveEquiv W₂ W₁)
    (hpair : Set.range eQ = φ.toAddEquiv '' Set.range eR)
    (hequivQ : ∀ x, RationalPointMap.pointAction W₁ (σQ (Q.rationalGenerator hQ))
      (eQ x) = eQ (Q.levelGenerator hQ x))
    (hequivR : ∀ x, RationalPointMap.pointAction W₂ (σR (R.rationalGenerator hR))
      (eR x) = eR (R.levelGenerator hR x))
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7) :
    σQ (Q.rationalGenerator hQ) * φ.conjugate hW₂ hW₁ (σR (R.rationalGenerator hR)) ≠
      φ.conjugate hW₂ hW₁ (σR (R.rationalGenerator hR)) * σQ (Q.rationalGenerator hQ) := by
  apply Q.rational_specializations_not_commute R hQ hR n hn W₁ hW₁ σQ
    ((φ.conjugate hW₂ hW₁).comp σR) eQ (φ.toAddEquiv.toAddMonoidHom.comp eR)
    heQ _ hequivQ _ hr hs
  · simpa only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom,
      Set.range_comp] using hpair
  · intro x
    change RationalPointMap.pointAction W₁
      (φ.conjugate hW₂ hW₁ (σR (R.rationalGenerator hR))) (φ.toAddEquiv (eR x)) = _
    rw [φ.conjugate_action, hequivR]
    rfl

end SptClassification.LevelSixForm
