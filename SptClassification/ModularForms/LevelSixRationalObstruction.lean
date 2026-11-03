/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixRationalEvaluation
public import SptClassification.Polynomials.SupersingularObstruction
import all SptClassification.ModularForms.LevelSixHasseGeometry

/-!
# The rational level-six Hasse root-count contradiction

The actual Hasse polynomial has `p-1` distinct geometric roots. The homogeneous
identity forces each root outside the two polynomial supports to be a root of
their Wronskian. Its degree bound contradicts the manuscript's class-number
inequality. Global construction of the rational sections remains separate.
[rolenManuscript, proof of Proposition 4.1]
-/

public noncomputable section

namespace SptClassification.LevelSixRationalObstruction

open Polynomial LevelSixRationalSections LevelSixRationalEvaluation
open LevelSixRationalHasseComparison

/-- Actual Hasse geometry and regular rational sections cannot satisfy the
homogeneous identity under the strict root-count bound. Regularity is required
only at Hasse zeros outside the two polynomial supports. -/
theorem no_homogeneous_identity {K : Type*} [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 3 < p) (h6 : (6 : K) ≠ 0) (h : ℕ) (A B : K[X])
    (hcop : IsCoprime A B) (hA : A.Monic) (hB : B.Monic)
    (hdegreeA : A.natDegree = 2 * h) (hdegreeB : B.natDegree = 2 * h)
    (hpositive : 0 < h) (hbound : 8 * h < p + 1)
    (L J : SectionRing K) (hL : IsWeight 2 L) (hJ : IsWeight 4 J) (d : ℕ)
    (hcoeff : L.coeff 2 = logarithmicCoefficient A B)
    (hregular : ∀ x : K, (LevelSixHasseGeometry.H p : K[X]).eval x = 0 →
      A.eval x ≠ 0 → B.eval x ≠ 0 → RegularAt x (J.coeff 4))
    (hidentity : corrected p (p + 3) (corrected p 2 L) =
      (d : SectionRing K) *
        (ofPolynomial (LevelSixHasseGeometry.hasseSection p) * corrected p 4 J)) :
    False := by
  classical
  let s := (LevelSixHasseGeometry.supersingularParameters (K := K) p).toFinset
  have hs : s.card = p - 1 := by
    simpa only [s, Set.toFinset_card] using
      LevelSixHasseGeometry.card_supersingularParameters (K := K) p hp h6
  apply no_supersingular_logarithmic_cover p h hcop hA hB hdegreeA hdegreeB
    hpositive hbound s hs
  intro x hx
  by_cases ha : A.IsRoot x
  · exact Or.inl ha
  by_cases hb : B.IsRoot x
  · exact Or.inr (Or.inl hb)
  have hroot : x ∈ (LevelSixHasseGeometry.H p : K[X]).rootSet K :=
    Set.mem_toFinset.mp hx
  have hH : (LevelSixHasseGeometry.H p : K[X]).eval x = 0 := by
    exact (Polynomial.mem_rootSet.mp hroot).2
  exact Or.inr (Or.inr (wronskian_eval_eq_zero_of_section_identity
    p hp h6 x A B L J hL hJ d hcoeff ha hb (hregular x hH ha hb) hH hidentity))

/-- The contradiction already follows from the Laurent differential identity:
fixed-weight Tate injectivity supplies the homogeneous Hasse identity. The
normalizing square root is the same one used by the actual Tate expansion. -/
theorem no_differential_identity {K : Type*} [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 3 < p) (h6 : (6 : K) ≠ 0) (h : ℕ) (A B : K[X])
    (hcop : IsCoprime A B) (hA : A.Monic) (hB : B.Monic)
    (hdegreeA : A.natDegree = 2 * h) (hdegreeB : B.natDegree = 2 * h)
    (hpositive : 0 < h) (hbound : 8 * h < p + 1)
    (r : K) (hr : r ^ 2 = -12)
    (L J : SectionRing K) (hL : IsWeight 2 L) (hJ : IsWeight 4 J) (d : ℕ)
    (hcoeff : L.coeff 2 = logarithmicCoefficient A B)
    (hregular : ∀ x : K, (LevelSixHasseGeometry.H p : K[X]).eval x = 0 →
      A.eval x ≠ 0 → B.eval x ≠ 0 → RegularAt x (J.coeff 4))
    (hdiff : LevelSixSerreExpansion.theta K
        (LevelSixSerreExpansion.theta K
          (LevelSixTateInjectivity.Rational.expansion K h6 r hr L)) =
      (d : LaurentSeries K) * LevelSixSerreExpansion.theta K
        (LevelSixTateInjectivity.Rational.expansion K h6 r hr J)) : False := by
  exact no_homogeneous_identity p hp h6 h A B hcop hA hB hdegreeA hdegreeB
    hpositive hbound L J hL hJ d hcoeff hregular
    (homogeneous_identity p hp h6 r hr L J hL hJ d hdiff)

end SptClassification.LevelSixRationalObstruction
