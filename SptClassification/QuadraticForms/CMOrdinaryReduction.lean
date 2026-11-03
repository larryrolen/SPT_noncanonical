/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMRationalPairSpecialization
public import SptClassification.QuadraticForms.OrdinaryRationalEndomorphisms

/-!
# Exclusion of ordinary common CM reduction

The manuscript's incompatible orientations force the geometric p-torsion
to vanish. The geometric specialization and marked isomorphism are explicit
inputs; the theorem does not assert their existence from an eta common root.
-/

public section

namespace SptClassification.LevelSixForm

/-- Compatible CM specializations with opposite orientation classes on
isomorphic marked curves have trivial geometric p-torsion on the first curve.
No condition on splitting of p in the CM field is needed. -/
theorem prime_torsion_eq_zero_of_rational_pair_specializations
    {D : ℤ} {r s : ZMod 12} [Fact (D < 0)]
    (Q : LevelSixForm D r) (R : LevelSixForm D s)
    (hQ : Q.b % 2 = 1) (hR : R.b % 2 = 1)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 - D)
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p]
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
    (hr : r = 1 ∨ r = 11) (hs : s = 5 ∨ s = 7)
    (P : W₁.toAffine.Point) (hpP : p • P = 0) : P = 0 := by
  exact RationalPointMap.prime_torsion_eq_zero_of_not_commute p W₁ hW₁ _ _
    (Q.rational_specializations_not_commute_of_pair_iso R hQ hR n hn
      W₁ W₂ hW₁ hW₂ σQ σR eQ eR heQ φ hpair hequivQ hequivR hr hs) P hpP

end SptClassification.LevelSixForm
