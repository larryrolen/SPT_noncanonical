/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMFormalProduct
public import SptClassification.ModularForms.LevelSixLogarithmicExpansion
public import SptClassification.ModularForms.LaurentHasseComparison
import all SptClassification.ModularForms.CMFormalProduct
import all SptClassification.ModularForms.LevelSixTateComparison
import all SptClassification.ModularForms.LevelSixTateInjectivity
import all SptClassification.ModularForms.LevelSixSerreExpansion
import Mathlib.Tactic.Ring

/-! # The CM product in the actual Laurent coordinate

Reversal removes the common pole of the two monic CM polynomials. Their
quotient and its logarithmic derivative therefore agree with the rational
sections used in the Hasse argument. [rolenManuscript, Section 4, (product), (L)]
-/

public noncomputable section
namespace SptClassification.CMLogarithmicLaurentComparison

open Polynomial LevelSixSerreExpansion LevelSixTateComparison LevelSixTateInjectivity

/-- Polynomial reversal evaluated in a field, with degree measured before
any coefficient reduction. -/
theorem eval_reverse_mul_pow {R F : Type*} [CommRing R] [Field F]
    (f : R →+* F) (P : R[X]) (t : F) (ht : t ≠ 0) :
    P.reverse.eval₂ f t⁻¹ * t ^ P.natDegree = P.eval₂ f t := by
  rw [Polynomial.eval₂_eq_sum_range' f (Nat.lt_succ_of_le P.reverse_natDegree_le),
    Finset.sum_mul, Polynomial.eval₂_eq_sum_range]
  rw [← Finset.sum_range_reflect (fun j => f (P.coeff j) * t ^ j) (P.natDegree + 1)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ P.natDegree := by simpa using Finset.mem_range.mp hj
  rw [Polynomial.coeff_reverse, Polynomial.revAt_le hj']
  have he : P.natDegree + 1 - 1 - j = P.natDegree - j := by omega
  rw [he]
  have hn : P.natDegree = j + (P.natDegree - j) := (Nat.add_sub_of_le hj').symm
  calc
    _ = f (P.coeff (P.natDegree - j)) * (t⁻¹ * t) ^ j *
        t ^ (P.natDegree - j) := by
      conv_lhs => rw [show t ^ P.natDegree = t ^ j * t ^ (P.natDegree - j) by
        rw [← pow_add, ← hn]]
      rw [mul_pow]
      ring
    _ = _ := by rw [inv_mul_cancel₀ ht, one_pow, mul_one]

variable {K : Type*} [Field K]

/-- Coefficient specialization followed by the canonical Laurent inclusion. -/
def seriesMap (f : CMFormalCoefficientRing →+* K) :
    PowerSeries CMFormalCoefficientRing →+* LaurentSeries K :=
  (tateBase K).comp (PowerSeries.map f)

theorem seriesMap_eulerUnit (f : CMFormalCoefficientRing →+* K) :
    seriesMap f (PowerSeries.map (algebraMap ℤ CMFormalCoefficientRing)
      levelSixFormalEulerUnit) = tateBase K (etaUnit K) := by
  change tateBase K (PowerSeries.map f (PowerSeries.map
    (algebraMap ℤ CMFormalCoefficientRing) levelSixFormalEulerUnit)) = _
  congr 1
  ext n
  simp [etaUnit]

theorem seriesMap_X (f : CMFormalCoefficientRing →+* K) :
    seriesMap f PowerSeries.X = q K := by
  simp [seriesMap, q]

theorem etaParameter_ne_zero : etaParameter K ≠ 0 := by
  intro h
  have := etaParameter_coeff_neg_one K
  simp [h] at this

/-- The reversed-polynomial variable becomes exactly the inverse eta coordinate. -/
theorem seriesMap_reciprocal (f : CMFormalCoefficientRing →+* K) :
    seriesMap f cmReciprocalEtaParameter = (etaParameter K)⁻¹ := by
  have h := congrArg (seriesMap f) cmReciprocalEtaParameter_mul_eulerUnit
  rw [map_mul, seriesMap_eulerUnit, seriesMap_X, ← q_mul_etaParameter] at h
  have hq : q K ≠ 0 := by
    simp [q, tateBase_apply]
  apply mul_right_cancel₀ (etaParameter_ne_zero (K := K))
  rw [inv_mul_cancel₀ etaParameter_ne_zero]
  apply mul_right_cancel₀ hq
  calc
    _ = seriesMap f cmReciprocalEtaParameter * (q K * etaParameter K) := by ring
    _ = q K := h
    _ = _ := by ring

/-- Reversal is compatible with specialization even when some coefficients vanish. -/
theorem seriesMap_reversed_mul_pow (f : CMFormalCoefficientRing →+* K)
    (P : CMFormalCoefficientRing[X]) :
    seriesMap f (cmReversedPolynomialEval P) * (etaParameter K) ^ P.natDegree =
      polynomialExpansion K (P.map f) := by
  rw [cmReversedPolynomialEval, Polynomial.hom_eval₂, seriesMap_reciprocal]
  have hc : (seriesMap f).comp PowerSeries.C = (constants K).comp f := by
    ext x
    simp [seriesMap, constants]
  rw [hc, eval_reverse_mul_pow _ _ _ etaParameter_ne_zero]
  simp [polynomialExpansion, Polynomial.eval₂_map]

/-- The actual normalized CM quotient is the quotient of the specialized
polynomials evaluated at the eta coordinate. -/
theorem seriesMap_cmQuotient (f : CMFormalCoefficientRing →+* K)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    seriesMap f (cmFormalBorcherdsQuotient d hd hsq hmod) =
      polynomialExpansion K (models.modelA.map f) /
        polynomialExpansion K (models.modelB.map f) := by
  dsimp only
  let models := integralCMClassPolynomials d hd hsq hmod
  have hdegree := cmIntegralOrientedPolynomial_equalDegree d hd hsq hmod
  have h := congrArg (seriesMap f)
    (cmFormalBorcherdsQuotient_mul_denominator d hd hsq hmod)
  dsimp only at hdegree h
  rw [map_mul] at h
  have hb := polynomialExpansion_ne_zero K (models.modelB.map f)
    (models.monicB.map f).ne_zero
  apply (eq_div_iff hb).mpr
  rw [← seriesMap_reversed_mul_pow, ← seriesMap_reversed_mul_pow]
  change seriesMap f (cmFormalBorcherdsQuotient d hd hsq hmod) *
      (seriesMap f (cmReversedPolynomialEval models.modelB) *
        etaParameter K ^ models.modelB.natDegree) =
    seriesMap f (cmReversedPolynomialEval models.modelA) *
      etaParameter K ^ models.modelA.natDegree
  rw [← mul_assoc, h, hdegree]

/-- A normalized power-series inverse maps to the field inverse. -/
theorem seriesMap_invOfUnit (f : CMFormalCoefficientRing →+* K)
    (F : PowerSeries CMFormalCoefficientRing) (hF : PowerSeries.constantCoeff F = 1) :
    seriesMap f (F.invOfUnit 1) = (seriesMap f F)⁻¹ := by
  have h := congrArg (seriesMap f) (PowerSeries.mul_invOfUnit F 1 hF)
  rw [map_mul, map_one] at h
  have hn : seriesMap f F ≠ 0 := by
    intro hz
    simp [hz] at h
  apply mul_left_cancel₀ hn
  rw [h, mul_inv_cancel₀ hn]

/-- Logarithmic differentiation commutes with coefficient specialization and
Laurent inclusion for the actual normalized unit. -/
theorem seriesMap_logarithmicDerivative (f : CMFormalCoefficientRing →+* K)
    (F : PowerSeries CMFormalCoefficientRing) (hF : PowerSeries.constantCoeff F = 1) :
    seriesMap f (QSeries.eulerDerivative F * F.invOfUnit 1) =
      theta K (seriesMap f F) / seriesMap f F := by
  rw [map_mul, seriesMap_invOfUnit f F hF, div_eq_mul_inv]
  congr 1
  change tateBase K (PowerSeries.map f (QSeries.eulerDerivative F)) =
    theta K (tateBase K (PowerSeries.map f F))
  rw [LaurentHasseComparison.theta_tateBase, QSeries.eulerDerivative_map]

/-- The rational weight-two CM section expands to the mapped logarithmic
Euler product, with the frame normalization retained. -/
theorem expansion_cmLogarithmicSection (f : CMFormalCoefficientRing →+* K)
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    Rational.expansion K h6 r hr
        (LevelSixLogarithmicExpansion.logarithmicSection
          (models.modelA.map f) (models.modelB.map f)) =
      seriesMap f (QSeries.eulerDerivative (cmFormalBorcherdsQuotient d hd hsq hmod) *
        (cmFormalBorcherdsQuotient d hd hsq hmod).invOfUnit 1) := by
  dsimp only
  let models := integralCMClassPolynomials d hd hsq hmod
  rw [LevelSixLogarithmicExpansion.expansion_logarithmicSection h6 r hr _ _
      (models.monicA.map f).ne_zero (models.monicB.map f).ne_zero,
    seriesMap_logarithmicDerivative f _
      (cmFormalBorcherdsQuotient_constantCoeff d hd hsq hmod),
    seriesMap_cmQuotient f d hd hsq hmod]

/-- The reduced actual CM logarithmic section is the principal Lambert row
used in the manuscript's coefficient argument. -/
theorem expansion_cmLogarithmicSection_mod
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6)
    (h6 : (6 : ZMod p) ≠ 0) (r : ZMod p) (hr : r ^ 2 = -12)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    Rational.expansion (ZMod p) h6 r hr
        (LevelSixLogarithmicExpansion.logarithmicSection
          (models.modelA.map (cmCoefficientReduction p hp6))
          (models.modelB.map (cmCoefficientReduction p hp6))) =
      tateBase (ZMod p) (QSeries.principalLogarithmicLambertSeries p d) := by
  dsimp only
  rw [expansion_cmLogarithmicSection]
  change tateBase (ZMod p) (PowerSeries.map (cmCoefficientReduction p hp6) _) = _
  rw [cmFormalBorcherdsQuotient_logarithmicLambert_mod_principal p d hp6 hd hsq hmod]

/-- The same comparison after any extension of the residue field. This permits
choosing the frame square root in an algebraic closure. -/
theorem expansion_cmLogarithmicSection_residueExtension
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6) (g : ZMod p →+* K)
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let f := g.comp (cmCoefficientReduction p hp6)
    let models := integralCMClassPolynomials d hd hsq hmod
    Rational.expansion K h6 r hr
        (LevelSixLogarithmicExpansion.logarithmicSection
          (models.modelA.map f) (models.modelB.map f)) =
      tateBase K (PowerSeries.map g (QSeries.principalLogarithmicLambertSeries p d)) := by
  dsimp only
  rw [expansion_cmLogarithmicSection]
  change tateBase K (PowerSeries.map (g.comp (cmCoefficientReduction p hp6)) _) = _
  have hmap (F : PowerSeries CMFormalCoefficientRing) :
      PowerSeries.map (g.comp (cmCoefficientReduction p hp6)) F =
        PowerSeries.map g (PowerSeries.map (cmCoefficientReduction p hp6) F) := by
    ext n
    simp
  rw [hmap, cmFormalBorcherdsQuotient_logarithmicLambert_mod_principal p d hp6 hd hsq hmod]

/-- The manuscript differential row persists under extension of the residue
field and the canonical Laurent inclusion. -/
theorem differential_residueExtension (p d : ℕ) [Fact p.Prime]
    (g : ZMod p →+* K)
    (hdiff : QSeries.eulerDerivative (QSeries.eulerDerivative
      (QSeries.principalLogarithmicLambertSeries p d)) =
        PowerSeries.C (d : ZMod p) *
          QSeries.eulerDerivative (QSeries.principalShimuraLambertSeries p d)) :
    theta K (theta K (tateBase K
      (PowerSeries.map g (QSeries.principalLogarithmicLambertSeries p d)))) =
      (d : LaurentSeries K) * theta K (tateBase K
        (PowerSeries.map g (QSeries.principalShimuraLambertSeries p d))) := by
  rw [LaurentHasseComparison.theta_tateBase, LaurentHasseComparison.theta_tateBase,
    QSeries.eulerDerivative_map, QSeries.eulerDerivative_map, hdiff,
    map_mul, map_mul, LaurentHasseComparison.theta_tateBase,
    QSeries.eulerDerivative_map]
  congr 1
  simp

/-- Once an independently constructed weight-four section has the actual
Shimura expansion, the coefficient identity is the differential identity for
the actual CM logarithmic section. -/
theorem differential_cmLogarithmicSection
    (p d : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6) (g : ZMod p →+* K)
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (J : LevelSixRationalSections.SectionRing K)
    (hJ : Rational.expansion K h6 r hr J =
      tateBase K (PowerSeries.map g (QSeries.principalShimuraLambertSeries p d)))
    (hdiff : QSeries.eulerDerivative (QSeries.eulerDerivative
      (QSeries.principalLogarithmicLambertSeries p d)) =
        PowerSeries.C (d : ZMod p) *
          QSeries.eulerDerivative (QSeries.principalShimuraLambertSeries p d)) :
    let f := g.comp (cmCoefficientReduction p hp6)
    let models := integralCMClassPolynomials d hd hsq hmod
    theta K (theta K (Rational.expansion K h6 r hr
      (LevelSixLogarithmicExpansion.logarithmicSection
        (models.modelA.map f) (models.modelB.map f)))) =
      (d : LaurentSeries K) * theta K (Rational.expansion K h6 r hr J) := by
  dsimp only
  rw [expansion_cmLogarithmicSection_residueExtension p d hp6 g h6 r hr hd hsq hmod, hJ]
  exact differential_residueExtension p d g hdiff

end SptClassification.CMLogarithmicLaurentComparison
