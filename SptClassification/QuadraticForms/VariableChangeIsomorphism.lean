/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.RationalCurveIsomorphism
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# The rational point isomorphism of an admissible coordinate change

The standard Weierstrass coordinate change supplies a rational additive
equivalence, with its action on affine points specified. This literature
interface does not descend marked points or specialize any endomorphism.
-/

public section

namespace SptClassification.RationalPointMap

/-- An admissible change of Weierstrass coordinates induces the corresponding
origin-preserving isomorphism [milne2021, Chapter II, Theorem 2.4(b), pp. 52–53].
The coordinate convention is `x = u²*x' + r`,
`y = u³*y' + u²*s*x' + t`. Preservation of the elliptic group law is
[milne2021, Chapter II, Proposition 1.5, p. 49]. Algebraic closedness ensures
the infinite geometric point groups required by `IsRational`.
This named literature admission fixes the map, including its action on marking.
-/
theorem exists_curveEquiv_of_variableChange
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W₁ W₂ : WeierstrassCurve F) (hW₂ : W₂.IsElliptic)
    (C : WeierstrassCurve.VariableChange F) (hC : C • W₂ = W₁) :
    ∃ e : CurveEquiv W₁ W₂,
      ∀ (x y : F) (hxy : W₁.toAffine.Nonsingular x y),
        ∃ hxy' : W₂.toAffine.Nonsingular
            ((C.u : F) ^ 2 * x + C.r)
            ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t),
          e.toAddEquiv (.some x y hxy) =
            .some ((C.u : F) ^ 2 * x + C.r)
              ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) hxy' := by
  sorry

/-- Conversely, a rational origin-preserving isomorphism of nonsingular
geometric Weierstrass curves is an admissible coordinate change
[milne2021, Chapter II, Theorem 2.4(b), pp. 52–53].

The rational descriptions in `CurveEquiv` extend across their finite exceptional
sets by [milne2021, Chapter I, Proposition 4.18 and Remark 4.19, p. 38].
Their inverse identities extend from the dense open sets. The resulting
isomorphisms agree with the supplied additive maps everywhere: the group-law
identity extends from a dense open subset of the product, and additive maps
on an infinite group agree if they agree outside a finite set. In particular
the extensions preserve the origin. Thus the theorem applies to these actual
point maps, not to unrelated rational functions. This is a named general
literature admission; it contains no assertion about a modular coordinate. -/
theorem exists_variableChange_of_curveEquiv
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (W₁ W₂ : WeierstrassCurve F) (hW₁ : W₁.IsElliptic) (hW₂ : W₂.IsElliptic)
    (e : CurveEquiv W₁ W₂) :
    ∃ (C : WeierstrassCurve.VariableChange F), C • W₂ = W₁ ∧
      ∀ (x y : F) (hxy : W₁.toAffine.Nonsingular x y),
        ∃ hxy' : W₂.toAffine.Nonsingular
            ((C.u : F) ^ 2 * x + C.r)
            ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t),
          e.toAddEquiv (.some x y hxy) =
            .some ((C.u : F) ^ 2 * x + C.r)
              ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) hxy' := by
  sorry

end SptClassification.RationalPointMap
