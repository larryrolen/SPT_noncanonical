/- Assembled by AxiomProver. -/

module

public import SptClassification.Polynomials.Wronskian

/-!
# A finite root count for the supersingular obstruction

The two degree-`2h` CM polynomials account for at most `4h` distinct
coordinates. At every remaining coordinate, logarithmic differentiation
forces a root of their nonzero Wronskian. This is the polynomial part of
[rolenManuscript, Section 4, proof of Proposition 4.1].
-/

public section

namespace SptClassification

open Polynomial

/-- A set covered by the roots of the two CM polynomials and their
logarithmic numerator has at most the sum of the three degree bounds.
The numerator is nonzero because the monic first polynomial has positive
degree below the characteristic and the two polynomials are coprime. -/
theorem logarithmicNumerator_cover_card_le {K : Type*} [Field K]
    (p : ℕ) [CharP K p] {A B : K[X]}
    (hcop : IsCoprime A B) (hA : A.Monic) (hB : B.Monic)
    (hdegree : B.natDegree = A.natDegree)
    (hpos : 0 < A.natDegree) (hlt : A.natDegree < p)
    (s : Finset K)
    (hcover : ∀ x ∈ s, A.IsRoot x ∨ B.IsRoot x ∨
      (A.derivative * B - A * B.derivative).IsRoot x) :
    s.card ≤ 2 * A.natDegree + (2 * A.natDegree - 2) := by
  classical
  let W : K[X] := A.derivative * B - A * B.derivative
  have hW : W ≠ 0 := logarithmicNumerator_ne_zero_of_char p hcop hA hpos hlt
  have hsubset : s ⊆ A.roots.toFinset ∪ B.roots.toFinset ∪ W.roots.toFinset := by
    intro x hx
    rcases hcover x hx with ha | hb | hw
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hA.ne_zero).mpr ha)))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hB.ne_zero).mpr hb)))
    · exact Finset.mem_union_right _
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hW).mpr hw))
  have hboundA : A.roots.toFinset.card ≤ A.natDegree := by
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
  have hboundB : B.roots.toFinset.card ≤ B.natDegree := by
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
  have hboundW : W.roots.toFinset.card ≤ 2 * A.natDegree - 2 := by
    exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans
        (natDegree_logarithmicNumerator_le hA hB hdegree hpos))
  have hcard := Finset.card_le_card hsubset
  have hsum : (A.roots.toFinset ∪ B.roots.toFinset ∪ W.roots.toFinset).card ≤
      A.roots.toFinset.card + B.roots.toFinset.card + W.roots.toFinset.card := by
    calc
      _ ≤ (A.roots.toFinset ∪ B.roots.toFinset).card + W.roots.toFinset.card :=
        Finset.card_union_le _ _
      _ ≤ A.roots.toFinset.card + B.roots.toFinset.card + W.roots.toFinset.card := by
        have h := Finset.card_union_le A.roots.toFinset B.roots.toFinset
        omega
  omega

/-- The manuscript's strict numerical inequality forbids the root cover
when both actual reduced CM polynomials have degree `2h`. -/
theorem no_supersingular_logarithmic_cover {K : Type*} [Field K]
    (p h : ℕ) [CharP K p] {A B : K[X]}
    (hcop : IsCoprime A B) (hA : A.Monic) (hB : B.Monic)
    (hdegreeA : A.natDegree = 2 * h)
    (hdegreeB : B.natDegree = 2 * h)
    (hpositive : 0 < h) (hbound : 8 * h < p + 1)
    (s : Finset K) (hcard : s.card = p - 1)
    (hcover : ∀ x ∈ s, A.IsRoot x ∨ B.IsRoot x ∨
      (A.derivative * B - A * B.derivative).IsRoot x) : False := by
  have hp : 0 < p := by omega
  have hdegpos : 0 < A.natDegree := by omega
  have hdeglt : A.natDegree < p := by omega
  have hsmall := logarithmicNumerator_cover_card_le p hcop hA hB
    (by omega) hdegpos hdeglt s hcover
  omega

end SptClassification
