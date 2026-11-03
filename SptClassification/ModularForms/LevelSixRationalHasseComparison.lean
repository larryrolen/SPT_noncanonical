/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixTateInjectivity
import all SptClassification.ModularForms.LevelSixRationalSections
import all SptClassification.ModularForms.LevelSixTateInjectivity
import Mathlib.Tactic.Ring

/-!
# Hasse comparison in the actual rational level-six section ring

The Hasse section, its Serre derivative and the Tate expansion use the same
eta coordinate and invariant differential. The only remaining inputs are the
independently constructed weight-two and weight-four rational sections and
their differential identity. [rolenManuscript, equation (hasse)]
-/

public noncomputable section

namespace SptClassification.LevelSixRationalHasseComparison

open Polynomial LevelSixRationalSections LevelSixSerreExpansion
open LevelSixTateInjectivity

variable {K : Type*} [Field K]

/-- Multiplication adds rational-section weights. -/
theorem weight_mul {k l : ℕ} {F G : SectionRing K}
    (hF : IsWeight k F) (hG : IsWeight l G) : IsWeight (k + l) (F * G) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  exact ⟨f * g, (sectionOf_mul k l f g).symm⟩

/-- Addition preserves a fixed weight. -/
theorem weight_add {k : ℕ} {F G : SectionRing K}
    (hF : IsWeight k F) (hG : IsWeight k G) : IsWeight k (F + G) := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  exact ⟨f + g, by simp [sectionOf, map_add]⟩

/-- A rational scalar coefficient has weight zero. -/
theorem weight_C (c : RatFunc K) : IsWeight 0 (C c) :=
  ⟨c, by simp [sectionOf]⟩

/-- Polynomial inclusion preserves the invariant differential weight. -/
theorem weight_ofPolynomial {k : ℕ} {F : LevelSixModularSections.SectionRing K}
    (hF : LevelSixModularSections.IsWeight k F) : IsWeight k (ofPolynomial F) := by
  obtain ⟨f, rfl⟩ := hF
  exact ⟨_, ofPolynomial_sectionOf k f⟩

/-- Hasse correction using the actual polynomial Hasse and Serre sections. -/
def corrected (p k : ℕ) (F : SectionRing K) : SectionRing K :=
  ofPolynomial (LevelSixHasseGeometry.hasseSection p) * serreSection k F +
    C ((k : RatFunc K) / 12) *
      ofPolynomial (LevelSixHasseGeometry.serreHasseSection p) * F

/-- The actual Hasse-corrected section has weight `k+p+1`. -/
theorem corrected_weight (p k : ℕ) (hp : 0 < p) (F : SectionRing K)
    (hF : IsWeight k F) : IsWeight (k + p + 1) (corrected p k F) := by
  have hH : IsWeight (p - 1)
      (ofPolynomial (LevelSixHasseGeometry.hasseSection (R := K) p)) := by
    exact weight_ofPolynomial (LevelSixHasseGeometry.hasseSection_weight p)
  have hE : IsWeight (p + 1)
      (ofPolynomial (LevelSixHasseGeometry.serreHasseSection (R := K) p)) := by
    exact weight_ofPolynomial (LevelSixHasseGeometry.serreHasseSection_weight_succ p hp)
  have hleft := weight_mul hH (serreSection_isWeight k F)
  have hright := weight_mul (weight_mul (weight_C ((k : RatFunc K) / 12)) hE) hF
  have hw : p - 1 + (k + 2) = k + p + 1 := by omega
  have hw' : 0 + (p + 1) + k = k + p + 1 := by omega
  rw [hw] at hleft
  rw [hw'] at hright
  exact weight_add hleft hright

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The actual correction has Euler derivative as Laurent expansion. -/
theorem expansion_corrected (hp : 3 < p) (h6 : (6 : K) ≠ 0)
    (r : K) (hr : r ^ 2 = -12) (k : ℕ) (F : SectionRing K)
    (hF : IsWeight k F) :
    Rational.expansion K h6 r hr (corrected p k F) =
      theta K (Rational.expansion K h6 r hr F) := by
  have hc : Rational.expansion K h6 r hr (C ((k : RatFunc K) / 12)) =
      (k : LaurentSeries K) / 12 := by
    simp [Rational.expansion, map_div₀, map_ofNat]
  rw [corrected, map_add, map_mul, map_mul, map_mul,
    Rational.expansion_hasse K p hp h6 r hr,
    Rational.expansion_serreHasse K p hp h6 r hr, hc, one_mul,
    Rational.expansion_serreSection K h6 r hr k F hF]
  exact sub_add_cancel _ _

/-- Fixed-weight Tate injectivity lifts the differential identity for the
actual rational Hasse sections. No global evaluation map or new literature
premise is introduced. -/
theorem homogeneous_identity (hp : 3 < p) (h6 : (6 : K) ≠ 0)
    (r : K) (hr : r ^ 2 = -12) (L J : SectionRing K)
    (hL : IsWeight 2 L) (hJ : IsWeight 4 J) (d : ℕ)
    (hdiff : theta K (theta K (Rational.expansion K h6 r hr L)) =
      (d : LaurentSeries K) * theta K (Rational.expansion K h6 r hr J)) :
    corrected p (p + 3) (corrected p 2 L) =
      (d : SectionRing K) *
        (ofPolynomial (LevelSixHasseGeometry.hasseSection p) * corrected p 4 J) := by
  have hL' : IsWeight (p + 3) (corrected p 2 L) := by
    have hw : 2 + p + 1 = p + 3 := by omega
    rw [← hw]
    exact corrected_weight p 2 (by omega) L hL
  have hleft : IsWeight (2 * p + 4) (corrected p (p + 3) (corrected p 2 L)) := by
    have hw : p + 3 + p + 1 = 2 * p + 4 := by omega
    rw [← hw]
    exact corrected_weight p (p + 3) (by omega) _ hL'
  have hH : IsWeight (p - 1)
      (ofPolynomial (LevelSixHasseGeometry.hasseSection (R := K) p)) := by
    exact weight_ofPolynomial (LevelSixHasseGeometry.hasseSection_weight p)
  have hd : IsWeight 0 (d : SectionRing K) := by simpa using weight_C (d : RatFunc K)
  have hright : IsWeight (2 * p + 4) ((d : SectionRing K) *
      (ofPolynomial (LevelSixHasseGeometry.hasseSection p) * corrected p 4 J)) := by
    have hw : 0 + (p - 1 + (4 + p + 1)) = 2 * p + 4 := by omega
    rw [← hw]
    exact weight_mul hd (weight_mul hH (corrected_weight p 4 (by omega) J hJ))
  apply Rational.expansion_injective_weight K h6 r hr (2 * p + 4) _ _ hleft hright
  rw [expansion_corrected p hp h6 r hr _ _ hL', expansion_corrected p hp h6 r hr _ _ hL,
    map_mul, map_mul, map_natCast, Rational.expansion_hasse K p hp h6 r hr,
    one_mul, expansion_corrected p hp h6 r hr _ _ hJ]
  exact hdiff

end SptClassification.LevelSixRationalHasseComparison
