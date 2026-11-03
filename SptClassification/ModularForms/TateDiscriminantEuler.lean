/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixRationalEtaClearing
public import SptClassification.ModularForms.CMLogarithmicLaurentComparison
public import SptClassification.ModularForms.CMShimuraCuspClearing
import all SptClassification.ModularForms.CMShimuraCuspClearing
import all SptClassification.ModularForms.CMLogarithmicLaurentComparison
import all SptClassification.ModularForms.LevelSixRationalEtaClearing
import all SptClassification.ModularForms.LevelSixTateComparison
import Mathlib.Tactic.Ring

/-! # The canonical Tate discriminant and the integral Euler expansion

The Tate equation uses the differential `dx/(2y+x)`. Its discriminant is
`q ∏ (1-q^n)^24`, without a factor of `12^6` or `(2πi)^12`.
The general Tate identity is the literature input; coefficient specialization
and the CM pole-clearing comparison below are algebraic deductions.
-/

public noncomputable section
namespace SptClassification.TateDiscriminantEuler

open LevelSixTateSections LevelSixSerreExpansion LevelSixTateComparison
  LevelSixTateInjectivity CMLogarithmicLaurentComparison

variable (K : Type*) [Field K]

/-- The discriminant product for the canonical Tate equation.
[silverman1994], Chapter V, §3, the Tate equation and discriminant product
`Δ(q)=q∏(1-q^n)^24`. The equation used here is also given in
[katz1973], Appendix A1.2.3, pp. 160–161. The identity is specialized from
the integral formal Tate equation to a field in which six is invertible.
The Silverman primary display has not been independently inspected in this
project; Katz's displayed equation alone is not a proof of the product. -/
theorem discriminant_euler_literature (h6 : (6 : K) ≠ 0) :
    (tateCurve K).Δ = PowerSeries.X *
      PowerSeries.map (Int.castRingHom K) (etaEulerSeries 1 ^ 24) := by
  sorry

/-- The same normalized discriminant in the Laurent target. -/
theorem delta_eq_euler (h6 : (6 : K) ≠ 0) :
    LevelSixRationalEtaClearing.delta K = q K *
      tateBase K (PowerSeries.map (Int.castRingHom K) (etaEulerSeries 1 ^ 24)) := by
  rw [LevelSixRationalEtaClearing.delta, discriminant_euler_literature K h6, map_mul]
  rfl

variable {K}

/-- Specializing the integral CM discriminant unit preserves its normalization. -/
theorem seriesMap_discriminant (f : CMFormalCoefficientRing →+* K)
    (h6 : (6 : K) ≠ 0) :
    q K * seriesMap f cmDiscriminantEulerUnit =
      LevelSixRationalEtaClearing.delta K := by
  rw [delta_eq_euler K h6]
  congr 1
  change tateBase K (PowerSeries.map f (PowerSeries.map
    (algebraMap ℤ CMFormalCoefficientRing) (etaEulerSeries 1 ^ 24))) = _
  have hmap : f.comp (algebraMap ℤ CMFormalCoefficientRing) = Int.castRingHom K := by
    ext n
    simp
  congr 1
  change ((PowerSeries.map f).comp
    (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing))) _ = _
  rw [← PowerSeries.map_comp, hmap]

/-- The pole-free polynomial cusp row is `q^degree(P) P(t)` after
specialization. The degree is taken before any coefficients are reduced. -/
theorem seriesMap_homogenization (f : CMFormalCoefficientRing →+* K)
    (P : Polynomial CMFormalCoefficientRing) :
    seriesMap f (cmPolynomialHomogenizationAtCusp P) =
      q K ^ P.natDegree * polynomialExpansion K (P.map f) := by
  rw [← cmReversedPolynomialEval_mul_eulerUnit_pow, map_mul, map_pow,
    seriesMap_eulerUnit, ← q_mul_etaParameter, mul_pow]
  calc
    _ = q K ^ P.natDegree * (seriesMap f (cmReversedPolynomialEval P) *
        etaParameter K ^ P.natDegree) := by ring
    _ = _ := by rw [seriesMap_reversed_mul_pow]

/-- The actual integral cleared Shimura row has exactly the rational
clearing factor, after any coefficient specialization. -/
theorem seriesMap_clearedShimura (f : CMFormalCoefficientRing →+* K)
    (h6 : (6 : K) ≠ 0) (d : ℕ) [Fact (-(d : ℤ) < 0)]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    seriesMap f (cmPoleClearedShimuraCuspSeries d hd hsq hmod) =
      (polynomialExpansion K (models.modelA.map f) *
        polynomialExpansion K (models.modelB.map f)) ^ 2 *
      LevelSixRationalEtaClearing.delta K ^ (8 * formClassNumber (-(d : ℤ))) *
      seriesMap f (cmIntegralShimuraCuspSeries d) := by
  dsimp only
  let models := integralCMClassPolynomials d hd hsq hmod
  let h := formClassNumber (-(d : ℤ))
  have hA : models.modelA.natDegree = 2 * h := models.degreeA hmod
  have hB : models.modelB.natDegree = 2 * h := models.degreeB hmod
  change seriesMap f (((cmPolynomialHomogenizationAtCusp models.modelA *
      cmPolynomialHomogenizationAtCusp models.modelB) ^ 2 *
      cmDiscriminantEulerUnit ^ (8 * h)) * cmIntegralShimuraCuspSeries d) = _
  simp only [map_mul, map_pow, seriesMap_homogenization]
  rw [hA, hB, ← seriesMap_discriminant f h6]
  simp only [mul_pow]
  have hq : (q K ^ (2 * h)) ^ 2 * (q K ^ (2 * h)) ^ 2 = q K ^ (8 * h) := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  calc
    _ = ((q K ^ (2 * h)) ^ 2 * (q K ^ (2 * h)) ^ 2) *
        (polynomialExpansion K (models.modelA.map f) ^ 2 *
          polynomialExpansion K (models.modelB.map f) ^ 2) *
        seriesMap f cmDiscriminantEulerUnit ^ (8 * h) *
        seriesMap f (cmIntegralShimuraCuspSeries d) := by ring
    _ = _ := by rw [hq]; ring

end SptClassification.TateDiscriminantEuler
