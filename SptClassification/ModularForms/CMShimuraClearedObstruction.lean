/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMShimuraRationalComparison
public import SptClassification.ModularForms.CMIntegralCuspComparison
public import SptClassification.ModularForms.CMLogarithmicLaurentComparison
public import SptClassification.ModularForms.LevelSixRationalObstruction
public import SptClassification.QuadraticForms.CMSeparation
public import SptClassification.QSeries.SquareCoefficientRelation
import SptClassification.QuadraticForms.CMIntegralValues
import all SptClassification.QSeries.ConditionalLambert
import all SptClassification.ModularForms.CMLogarithmicLaurentComparison

/-! # Character obstruction from a globally holomorphic CM clearing

The only additional analytic input is a holomorphic modular form of weight
`96*h(-d)+4` with the independently specified integral cleared Shimura row.
The eta numerator, reduction, rational regularity, and Hasse contradiction
are deductions. Existing named literature premises remain in the dependency
cone. [rolenManuscript, proof of Proposition 4.1]
-/

public noncomputable section

namespace SptClassification.CMShimuraClearedObstruction

open LevelSixSerreExpansion LevelSixTateInjectivity
  CMLogarithmicLaurentComparison LevelSixRationalEtaClearing

/-- Character-class vanishing forces the differential identity of the actual
principal Lambert rows, using the manuscript's square-coefficient theorem. -/
theorem principal_differential_of_vanishing
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hd : 0 < d)
    (hmod : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j) :
    QSeries.eulerDerivative (QSeries.eulerDerivative
      (QSeries.principalLogarithmicLambertSeries p d)) =
      PowerSeries.C (d : ZMod p) *
        QSeries.eulerDerivative (QSeries.principalShimuraLambertSeries p d) := by
  apply QSeries.eulerDerivative_twice_logarithmicLambert p (d : ZMod p)
    (fun n => (QSeries.principalHFourier d (QSeries.fFourier d) (n : ℤ) : ZMod p))
    (fun n => (QSeries.principalKFourier d (n : ℤ) : ZMod p))
  intro m hm hmcop
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    (QSeries.square_coefficient_relation p hp sign hsign d hd hmod hr hspt m hm hmcop)
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Nat.cast_pow]
    using hc

/-- A coefficient specialization of a genuine holomorphic clearing suffices
for the character obstruction. All geometric and Hasse data are constructed
from the actual CM polynomials. -/
theorem obstruction_of_residue_clearing
    {K : Type*} [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 5 ≤ p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1)
    (hp6 : ¬p ∣ 6) (g : ZMod p →+* K)
    (h6 : (6 : K) ≠ 0) (r : K) (hrsq : r ^ 2 = -12)
    (R : Subring ℂ) (i : CMFormalCoefficientRing →+* R) (f : R →+* K)
    (hcompat : f.comp i = g.comp (cmCoefficientReduction p hp6))
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ))
      ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ))
    (hrow : PowerSeries.map R.subtype
        (PowerSeries.map i (cmPoleClearedShimuraCuspSeries d hd hsq hmod)) =
      UpperHalfPlane.qExpansion 1 (fun z => F z)) :
    ¬∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j := by
  intro hspt
  let models := integralCMClassPolynomials d hd hsq hmod
  let φ := g.comp (cmCoefficientReduction p hp6)
  let A := models.modelA.map φ
  let B := models.modelB.map φ
  have hd22 : 22 ≤ d := by omega
  have hmul : 22 * d ≤ d * d := Nat.mul_le_mul_right d hd22
  have hdlt : d < p := by nlinarith [hmul]
  have hcop : ¬p ∣ 6 * d := by
    intro h
    rcases (Fact.out : p.Prime).dvd_mul.mp h with h6 | hpd
    · exact hp6 h6
    · exact (Nat.not_dvd_of_pos_of_lt hd hdlt) hpd
  have hAB : IsCoprime A B := by
    have h := (cm_separation d p hd hsq hmod hcop hsep).map (Polynomial.mapRingHom g)
    simpa only [Polynomial.coe_mapRingHom, Polynomial.map_map] using h
  obtain ⟨P, _hdeg, hP⟩ := CMShimuraRationalComparison.numerator_of_holomorphic_clearing
    R i f h6 r hrsq d hd hsq hmod F hrow
  rw [hcompat] at hP
  let J := rationalSection (formClassNumber (-(d : ℤ))) A B (P.map f)
  have hJ : Rational.expansion K h6 r hrsq J =
      tateBase K (PowerSeries.map g (QSeries.principalShimuraLambertSeries p d)) := by
    rw [show Rational.expansion K h6 r hrsq J =
      seriesMap φ (cmIntegralShimuraCuspSeries d) from hP]
    change tateBase K (PowerSeries.map φ _) = _
    have hm (U : PowerSeries CMFormalCoefficientRing) :
        PowerSeries.map φ U = PowerSeries.map g
          (PowerSeries.map (cmCoefficientReduction p hp6) U) := by
      ext n
      simp [φ]
    rw [hm, cmIntegralShimuraCuspSeries_reduction p d hp6]
  have hdiff := differential_cmLogarithmicSection p d hp6 g h6 r hrsq hd hsq hmod
    J hJ (principal_differential_of_vanishing p hp sign hsign d hd hmod hr hspt)
  apply LevelSixRationalObstruction.no_differential_identity p (by omega) h6
    (formClassNumber (-(d : ℤ))) A B hAB (models.monicA.map φ) (models.monicB.map φ)
    ((models.monicA.natDegree_map φ).trans (models.degreeA hmod))
    ((models.monicB.natDegree_map φ).trans (models.degreeB hmod))
    (formClassNumber_pos _ (by omega)) hclass r hrsq
    (LevelSixLogarithmicExpansion.logarithmicSection A B) J
    (LevelSixLogarithmicExpansion.logarithmicSection_weight A B)
    (section_weight _ A B (P.map f)) d
    (LevelSixLogarithmicExpansion.logarithmicSection_coeff A B) _ hdiff
  intro x hx ha hb
  change LevelSixRationalEvaluation.RegularAt x (J.coeff 4)
  rw [show J.coeff 4 = coefficient (formClassNumber (-(d : ℤ))) A B (P.map f) from
    section_coeff _ A B (P.map f)]
  exact regularAt_hasse_zero p (by omega) h6 _ A B (P.map f) x hx (mul_ne_zero ha hb)

/-- The actual complex image of the localized integral CM coefficient ring. -/
def complexCoefficientRing : Subring ℂ := cmCoefficientComplexMap.range

/-- The complex coefficient subring retains exactly `ℤ[1/6]`, so its residue
specialization does not require an additional integrality hypothesis. -/
def complexCoefficientEquiv : CMFormalCoefficientRing ≃+* complexCoefficientRing :=
  RingEquiv.ofBijective cmCoefficientComplexMap.rangeRestrict ⟨by
    intro x y h
    exact CMIntegralValues.coefficientMap_injective (congrArg Subtype.val h), by
    intro y
    obtain ⟨x, hx⟩ := y.property
    exact ⟨x, Subtype.ext hx⟩⟩

theorem complexCoefficientEquiv_subtype (x : CMFormalCoefficientRing) :
    complexCoefficientRing.subtype (complexCoefficientEquiv x) =
      cmCoefficientComplexMap x := (rfl)

/-- A genuine globally holomorphic cleared modular form with the actual CM
Shimura Fourier row implies the manuscript's character obstruction. The
bounds and class number are unchanged. No separate good-reduction data,
Hasse structure, coefficient-ring choice, or global rational `J` is assumed.
[rolenManuscript, Proposition 4.1] -/
theorem obstruction_of_holomorphic_clearing
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1)
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ))
      ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ))
    (hrow : PowerSeries.map cmCoefficientComplexMap
        (cmPoleClearedShimuraCuspSeries d hd hsq hmod) =
      UpperHalfPlane.qExpansion 1 (fun z => F z)) :
    ¬∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j := by
  have hp6 : ¬p ∣ 6 := by
    intro h
    have h23 : p ∣ 2 ∨ p ∣ 3 := by
      apply (Fact.out : p.Prime).dvd_mul.mp
      simpa only [show 2 * 3 = 6 by decide] using h
    rcases h23 with h2 | h3
    · have := Nat.le_of_dvd (by decide : 0 < 2) h2
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega
  let K := AlgebraicClosure (ZMod p)
  let g : ZMod p →+* K := algebraMap (ZMod p) K
  have h6 : (6 : K) ≠ 0 := by
    intro hz
    apply hp6
    apply (ZMod.natCast_eq_zero_iff 6 p).mp
    apply g.injective
    simpa only [map_natCast, map_ofNat, map_zero, Nat.cast_ofNat] using hz
  obtain ⟨r, hrsq⟩ := IsAlgClosed.exists_pow_nat_eq (-12 : K) (by decide : 0 < 2)
  let i := complexCoefficientEquiv.toRingHom
  let f := (g.comp (cmCoefficientReduction p hp6)).comp
    complexCoefficientEquiv.symm.toRingHom
  have hcompat : f.comp i = g.comp (cmCoefficientReduction p hp6) := by
    ext x
    change g (cmCoefficientReduction p hp6
      (complexCoefficientEquiv.symm (complexCoefficientEquiv x))) = _
    simp only [RingEquiv.symm_apply_apply, RingHom.comp_apply]
  apply obstruction_of_residue_clearing p hp sign hsign d hd hsq hmod hr
    hsep hclass hp6 g h6 r hrsq complexCoefficientRing i f hcompat F
  have hm (U : PowerSeries CMFormalCoefficientRing) :
      PowerSeries.map complexCoefficientRing.subtype (PowerSeries.map i U) =
        PowerSeries.map cmCoefficientComplexMap U := by
    ext n
    simp only [PowerSeries.coeff_map]
    exact complexCoefficientEquiv_subtype _
  rw [hm]
  exact hrow

/-- A globally holomorphic clearing of the actual convergent Shimura lift
implies character obstruction. The Fourier row follows from high-cusp
uniqueness; the same `J` occurs in its convergent series and in the clearing.
[rolenManuscript, Section 4, proof of prop:obstruction] -/
theorem obstruction_of_highCusp_clearing
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1)
    (F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
      (Matrix.SpecialLinearGroup.mapGL ℝ))
      ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ))
    (J : UpperHalfPlane → ℂ) (YJ YF : ℝ)
    (hJ : ∀ z : UpperHalfPlane, YJ < z.im →
      HasSum (fun n => ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
        Function.Periodic.qParam 1 z ^ n) (J z))
    (hF : ∀ z : UpperHalfPlane, YF < z.im →
      F z = ((cmClassPolynomialA (-(d : ℤ))).eval (levelSixEtaQuotient z) *
        (cmClassPolynomialB (-(d : ℤ))).eval (levelSixEtaQuotient z)) ^ 2 *
          ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) * J z) :
    ¬∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j := by
  exact obstruction_of_holomorphic_clearing p hp sign hsign d hd hsq hmod hr
    hsep hclass F
    (cmPoleClearedShimuraCuspSeries_eq_qExpansion d hd hsq hmod F J YJ YF hJ hF)

end SptClassification.CMShimuraClearedObstruction
