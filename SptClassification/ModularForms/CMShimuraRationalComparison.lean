/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.TateDiscriminantEuler
public import SptClassification.ModularForms.LevelSixEtaPolynomialLaurent
import all SptClassification.ModularForms.CMLogarithmicLaurentComparison

/-! # The rational section of an independently cleared CM Shimura lift

A globally holomorphic cleared form with the actual integral Fourier row has
an eta-polynomial numerator. Specialization and the normalized Tate
identity recover the uncleared weight-four expansion. The analytic existence
and all-cusp holomorphy of the cleared form are explicit inputs, not admissions.
[rolenManuscript, proof of prop:obstruction, pole-clearing paragraph]
-/

public noncomputable section
namespace SptClassification.CMShimuraRationalComparison

open LevelSixSerreExpansion LevelSixTateInjectivity
  CMLogarithmicLaurentComparison LevelSixRationalEtaClearing

variable {K : Type*} [Field K]

/-- An eta numerator for the actual integral cleared row determines the
weight-four rational section after any coefficient specialization. -/
theorem expansion_of_cleared_row
    (R : Type*) [CommRing R] (i : CMFormalCoefficientRing →+* R) (f : R →+* K)
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (P : Polynomial R)
    (hdeg : P.natDegree ≤ 96 * formClassNumber (-(d : ℤ)) + 4)
    (hrow : PowerSeries.map i (cmPoleClearedShimuraCuspSeries d hd hsq hmod) =
      LevelSixEtaPolynomialLaurent.polynomialSeries
        (96 * formClassNumber (-(d : ℤ)) + 4) P) :
    let models := integralCMClassPolynomials d hd hsq hmod
    Rational.expansion K h6 r hr
      (rationalSection (formClassNumber (-(d : ℤ)))
        (models.modelA.map (f.comp i)) (models.modelB.map (f.comp i)) (P.map f)) =
      seriesMap (f.comp i) (cmIntegralShimuraCuspSeries d) := by
  dsimp only
  let models := integralCMClassPolynomials d hd hsq hmod
  apply expansion_eq_of_cleared_identity K h6 r hr _ _ _ _
    (models.monicA.map (f.comp i)).ne_zero (models.monicB.map (f.comp i)).ne_zero
  rw [← TateDiscriminantEuler.seriesMap_clearedShimura (f.comp i) h6 d hd hsq hmod]
  change tateBase K (PowerSeries.map (f.comp i) _) = _
  have hm (F : PowerSeries CMFormalCoefficientRing) :
      PowerSeries.map (f.comp i) F = PowerSeries.map f (PowerSeries.map i F) := by
    ext n
    simp
  rw [hm, hrow]
  exact LevelSixEtaPolynomialLaurent.tateBase_map_polynomialSeries K f _ P hdeg

/-- The global holomorphic cleared lift and its actual Fourier row supply
an independent numerator and the desired rational expansion. The coefficient
ring may be any complex subring admitting the chosen residue map. -/
theorem numerator_of_holomorphic_clearing
    (R : Subring ℂ) (i : CMFormalCoefficientRing →+* R) (f : R →+* K)
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23)
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ))
      ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ))
    (hrow : PowerSeries.map R.subtype
        (PowerSeries.map i (cmPoleClearedShimuraCuspSeries d hd hsq hmod)) =
      UpperHalfPlane.qExpansion 1 (fun z => F z)) :
    ∃ P : Polynomial R, P.natDegree ≤ 96 * formClassNumber (-(d : ℤ)) + 4 ∧
      let models := integralCMClassPolynomials d hd hsq hmod
      Rational.expansion K h6 r hr
        (rationalSection (formClassNumber (-(d : ℤ)))
          (models.modelA.map (f.comp i)) (models.modelB.map (f.comp i)) (P.map f)) =
        seriesMap (f.comp i) (cmIntegralShimuraCuspSeries d) := by
  have heven : Even (96 * formClassNumber (-(d : ℤ)) + 4) := by
    exact ⟨48 * formClassNumber (-(d : ℤ)) + 2, by omega⟩
  obtain ⟨P, hdeg, _, hP⟩ := LevelSixEtaPolynomialLaurent.holomorphic_basis_with_series
    R _ heven F _ hrow
  exact ⟨P, hdeg, expansion_of_cleared_row R i f h6 r hr d hd hsq hmod P hdeg hP⟩

end SptClassification.CMShimuraRationalComparison
