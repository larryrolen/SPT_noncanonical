/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMIntegralValues
public import SptClassification.QuadraticForms.RationalEndomorphisms

/-!
# Endomorphisms and integral sections under good reduction

The integral closure fixes both the complex embedding and the chosen residue
place. The interface below applies to arbitrary nonsingular Weierstrass curves;
it contains no CM discriminant, modular coordinate, or separation conclusion.
-/

public section

namespace SptClassification.RationalPointMap

/-- Good reduction specializes geometric endomorphisms and preserves their
equalities on integral sections.

This is the coordinate corollary of [milneAV2008, Chapter I, Corollary 16.4(b),
p. 68; Theorem 17.1 and Remark 17.2, p. 70; Theorem 17.3, p. 71], rather than a
verbatim statement of any one of those results. A rational endomorphism over
`ℂ` descends first to a finitely generated extension of the algebraic closure
of `ℚ`; that extension is regular, so Corollary 16.4(b) descends it to algebraic
coefficients. The equation, endomorphism, and sections then descend to a number
field. The restriction of `red` chooses its residue place. The nonsingular
equation is a good model there; the Néron mapping property extends the
endomorphism uniquely. Uniqueness preserves addition, composition, and its
action on sections. Theorem 17.3 makes this compatible with further finite
extensions, giving the single geometric endomorphism specialization below.

The equalities `hc` and `hr` retain the actual equations, and the affine
coordinates of both sections are related by the specified maps. No reduction
map on arbitrary complex points is asserted. The rational-point-map
interpretation uses extension of rational maps on smooth projective curves as
in [silverman2009, Chapter II, §2], already recorded in `RationalEndomorphisms`.
This named literature interface remains a visible admission. -/
theorem goodReduction_endomorphisms_sections_literature
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : 3 < p)
    (red : CMIntegralValues.Ring →+* F)
    (W : WeierstrassCurve CMIntegralValues.Ring)
    (E : WeierstrassCurve ℂ) (Ebar : WeierstrassCurve F)
    (hc : W.map CMIntegralValues.complexEmbedding = E)
    (hr : W.map red = Ebar) (hE : E.IsElliptic) (hEbar : Ebar.IsElliptic) :
    ∃ σ : endomorphismRing E →+* endomorphismRing Ebar,
      ∀ (x y : CMIntegralValues.Ring)
        (hxy : E.toAffine.Nonsingular
          (CMIntegralValues.complexEmbedding x) (CMIntegralValues.complexEmbedding y))
        (hred : Ebar.toAffine.Nonsingular (red x) (red y))
        (a : endomorphismRing E) (m : ℤ),
        pointAction E a (.some _ _ hxy) = m • (.some _ _ hxy) →
        pointAction Ebar (σ a) (.some _ _ hred) = m • (.some _ _ hred) := by
  sorry

end SptClassification.RationalPointMap
