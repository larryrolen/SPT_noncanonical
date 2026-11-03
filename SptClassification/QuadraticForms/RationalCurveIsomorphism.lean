/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.RationalEndomorphisms

/-!
# Rational isomorphisms of elliptic curves and their endomorphisms

An isomorphism acts on the actual point groups and has compatible rational
coordinates in both directions. Conjugation therefore transports the actual
rational endomorphism rings. This allows reduced CM pairs to be compared up to
isomorphism, without choosing identical Weierstrass equations.
-/

public section

namespace SptClassification.RationalPointMap

variable {F : Type*} [Field F] [DecidableEq F]

/-- Composition of algebraic maps of smooth projective curves, applied to
elliptic curves [silverman2009, Chapter II, §2; Chapter III, §4]. The rational
coordinates describe the supplied additive maps off finite exceptional sets;
extension and additive uniqueness identify their values everywhere. A nonzero
map is nonconstant, so the inverse image of a finite exceptional set is finite.
This is a general literature premise, with section-level locators only; no
primary theorem number has been independently verified. -/
theorem isRational_comp [IsAlgClosed F]
    {W₁ W₂ W₃ : WeierstrassCurve F}
    (hW₁ : W₁.IsElliptic) (hW₂ : W₂.IsElliptic) (hW₃ : W₃.IsElliptic)
    (f : W₂.toAffine.Point →+ W₃.toAffine.Point)
    (g : W₁.toAffine.Point →+ W₂.toAffine.Point)
    (hf : IsRational f) (hg : IsRational g) : IsRational (f.comp g) := by
  sorry

/-- An additive equivalence with rational coordinates for the same point maps
in both directions. Over smooth geometric elliptic curves these are precisely
the origin-preserving algebraic isomorphisms. -/
structure CurveEquiv (W₁ W₂ : WeierstrassCurve F) where
  toAddEquiv : W₁.toAffine.Point ≃+ W₂.toAffine.Point
  rational : IsRational toAddEquiv.toAddMonoidHom
  inverse_rational : IsRational toAddEquiv.symm.toAddMonoidHom

namespace CurveEquiv

variable {W₁ W₂ : WeierstrassCurve F}

/-- Reverse the actual rational isomorphism. -/
def symm (e : CurveEquiv W₁ W₂) : CurveEquiv W₂ W₁ where
  toAddEquiv := e.toAddEquiv.symm
  rational := e.inverse_rational
  inverse_rational := e.rational

theorem symm_toAddEquiv (e : CurveEquiv W₁ W₂) :
    e.symm.toAddEquiv = e.toAddEquiv.symm := (rfl)

/-- Conjugation carries rational endomorphisms between the two actual curves. -/
noncomputable def conjugate [IsAlgClosed F]
    (e : CurveEquiv W₁ W₂) (hW₁ : W₁.IsElliptic) (hW₂ : W₂.IsElliptic) :
    endomorphismRing W₁ →+* endomorphismRing W₂ where
  toFun f := ofRational
    (e.toAddEquiv.toAddMonoidHom.comp
      ((pointAction W₁ f).comp e.toAddEquiv.symm.toAddMonoidHom))
    (isRational_comp hW₂ hW₁ hW₂ _ _ e.rational
      (isRational_comp hW₂ hW₁ hW₁ _ _
        (endomorphismRing_isRational W₁ hW₁ f) e.inverse_rational))
  map_one' := by
    apply pointAction_injective W₂
    erw [pointAction_ofRational]
    ext x
    change e.toAddEquiv (pointAction W₁ 1 (e.toAddEquiv.symm x)) =
      pointAction W₂ 1 x
    simp
  map_mul' f g := by
    apply pointAction_injective W₂
    erw [pointAction_ofRational]
    simp only [map_mul]
    erw [pointAction_ofRational, pointAction_ofRational]
    ext x
    change e.toAddEquiv (pointAction W₁ f (pointAction W₁ g (e.toAddEquiv.symm x))) =
      e.toAddEquiv (pointAction W₁ f
        (e.toAddEquiv.symm (e.toAddEquiv (pointAction W₁ g (e.toAddEquiv.symm x)))))
    simp
  map_zero' := by
    apply pointAction_injective W₂
    erw [pointAction_ofRational]
    ext x
    change e.toAddEquiv (pointAction W₁ 0 (e.toAddEquiv.symm x)) =
      pointAction W₂ 0 x
    simp
  map_add' f g := by
    apply pointAction_injective W₂
    erw [pointAction_ofRational]
    simp only [map_add]
    erw [pointAction_ofRational, pointAction_ofRational]
    ext x
    change e.toAddEquiv (pointAction W₁ f (e.toAddEquiv.symm x) +
      pointAction W₁ g (e.toAddEquiv.symm x)) =
      e.toAddEquiv (pointAction W₁ f (e.toAddEquiv.symm x)) +
        e.toAddEquiv (pointAction W₁ g (e.toAddEquiv.symm x))
    simp

/-- The conjugated map is compatible with the very same point isomorphism. -/
theorem conjugate_action [IsAlgClosed F]
    (e : CurveEquiv W₁ W₂) (hW₁ : W₁.IsElliptic) (hW₂ : W₂.IsElliptic)
    (f : endomorphismRing W₁) (x : W₁.toAffine.Point) :
    pointAction W₂ (e.conjugate hW₁ hW₂ f) (e.toAddEquiv x) =
      e.toAddEquiv (pointAction W₁ f x) := by
  change pointAction W₂ (ofRational _ _) (e.toAddEquiv x) = _
  erw [pointAction_ofRational]
  change e.toAddEquiv (pointAction W₁ f (e.toAddEquiv.symm (e.toAddEquiv x))) = _
  rw [e.toAddEquiv.symm_apply_apply]

/-- Conjugation retains the entire rational endomorphism, not just its
restriction to the marked finite subgroup. -/
theorem conjugate_injective [IsAlgClosed F]
    (e : CurveEquiv W₁ W₂) (hW₁ : W₁.IsElliptic) (hW₂ : W₂.IsElliptic) :
    Function.Injective (e.conjugate hW₁ hW₂) := by
  intro f g hfg
  apply pointAction_injective W₁
  ext x
  apply e.toAddEquiv.injective
  rw [← e.conjugate_action hW₁ hW₂ f x, ← e.conjugate_action hW₁ hW₂ g x, hfg]

end CurveEquiv
end SptClassification.RationalPointMap
