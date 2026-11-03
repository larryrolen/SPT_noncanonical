/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.RationalEndomorphisms

/-!
# Ordinary reduction and rational endomorphisms

The ordinary endomorphism theorem is a named literature input. Its
contrapositive gives the geometric p-torsion criterion needed after the
manuscript's orientation argument. All maps act on the actual curve points.
-/

public section

namespace SptClassification.RationalPointMap

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]

/-- Ordinary elliptic curves have commutative geometric endomorphism rings
[silverman2009, Chapter V, §3; Chapter III, §9]. Here ordinarity is expressed
by a nonzero geometric point killed by the positive characteristic prime.
The compatible rational descriptions extend to algebraic maps of the smooth
projective cubic, and additivity fixes their values at exceptional points.
This is a visible literature admission. The section locators are retained;
the theorem numbers suggested by indexed references were not independently
verified against the primary text. -/
theorem comp_comm_of_nonzero_prime_torsion
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (W : WeierstrassCurve F) (hW : W.IsElliptic)
    (P : W.toAffine.Point) (hP : P ≠ 0) (hpP : p • P = 0)
    (f g : AddMonoid.End W.toAffine.Point)
    (hf : IsRational f) (hg : IsRational g) :
    f.comp g = g.comp f := by
  sorry

/-- Noncommuting rational endomorphisms exclude every nonzero geometric
p-torsion point. This is the supersingular p-torsion criterion, expressed
without introducing a separate ordinary/supersingular predicate. -/
theorem prime_torsion_eq_zero_of_not_commute
    (p : ℕ) [Fact p.Prime] [CharP F p]
    (W : WeierstrassCurve F) (hW : W.IsElliptic)
    (f g : endomorphismRing W) (hne : f * g ≠ g * f)
    (P : W.toAffine.Point) (hpP : p • P = 0) : P = 0 := by
  by_contra hP
  apply hne
  apply pointAction_injective W
  rw [map_mul, map_mul]
  exact comp_comm_of_nonzero_prime_torsion p W hW P hP hpP
    (pointAction W f) (pointAction W g)
    (endomorphismRing_isRational W hW f) (endomorphismRing_isRational W hW g)

end SptClassification.RationalPointMap
