/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixTateComparison
public import SptClassification.ModularForms.LevelSixRationalSections
public import SptClassification.ModularForms.LevelSixLaurentDerivation
import all SptClassification.ModularForms.LevelSixRationalSections
import all SptClassification.ModularForms.LevelSixSerreExpansion
import all SptClassification.ModularForms.LevelSixTateComparison
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public noncomputable section

namespace SptClassification.LevelSixTateInjectivity

open Polynomial LevelSixSerreExpansion LevelSixTateComparison

variable (K : Type*) [Field K]

/-- The eta coordinate has precisely its expected simple pole. -/
theorem etaParameter_order : (etaParameter K).order = -1 := by
  have hn : etaParameter K ≠ 0 := by
    intro h
    have := etaParameter_coeff_neg_one K
    simp [h] at this
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by simp)
  · apply (HahnSeries.le_order_iff_forall hn).mpr
    intro j hj
    rw [etaParameter, HahnSeries.coeff_single_mul, one_mul, tateBase_apply]
    change ((etaUnit K : PowerSeries K) : LaurentSeries K).coeff (j - -1) = 0
    rw [PowerSeries.coeff_coe, if_pos (by omega)]

/-- Substitution at the actual eta Laurent coordinate. -/
def polynomialExpansion : K[X] →+* LaurentSeries K :=
  eval₂RingHom (constants K) (etaParameter K)

theorem polynomialExpansion_ne_zero (P : K[X]) (hP : P ≠ 0) :
    polynomialExpansion K P ≠ 0 := by
  have ht : etaParameter K ≠ 0 := by
    intro h
    have := etaParameter_coeff_neg_one K
    simp [h] at this
  have hord (n : ℕ) : ((etaParameter K) ^ n).order = -(n : ℤ) := by
    rw [HahnSeries.order_pow, etaParameter_order]
    simp
  have htop : ((etaParameter K) ^ P.natDegree).coeff (-(P.natDegree : ℤ)) ≠ 0 := by
    rw [← hord, Ne, HahnSeries.coeff_order_eq_zero]
    exact pow_ne_zero _ ht
  have hc : (polynomialExpansion K P).coeff (-(P.natDegree : ℤ)) =
      P.leadingCoeff * ((etaParameter K) ^ P.natDegree).coeff (-(P.natDegree : ℤ)) := by
    change (eval₂ (constants K) (etaParameter K) P).coeff _ = _
    rw [eval₂_eq_sum_range, HahnSeries.coeff_sum]
    rw [Finset.sum_eq_single P.natDegree]
    · simp [constants_apply, HahnSeries.coeff_single_mul, coeff_natDegree]
    · intro n hn hnd
      have hlt : n < P.natDegree := by
        have := Finset.mem_range.mp hn
        omega
      rw [constants_apply, HahnSeries.coeff_single_mul, sub_zero,
        HahnSeries.coeff_eq_zero_of_lt_order (by rw [hord]; omega), mul_zero]
    · simp
  intro h
  rw [h, HahnSeries.coeff_zero] at hc
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hP) htop hc.symm

theorem polynomialExpansion_injective : Function.Injective (polynomialExpansion K) := by
  intro P Q h
  have hz : polynomialExpansion K (P - Q) = 0 := by rw [map_sub, h, sub_self]
  by_contra hpq
  exact polynomialExpansion_ne_zero K (P - Q) (sub_ne_zero.mpr hpq) hz

/-- The eta substitution extends uniquely to the rational coefficient field.
Injectivity, rather than evaluation at an arbitrary point, justifies this map. -/
def coefficientExpansion : RatFunc K →+* LaurentSeries K :=
  RatFunc.liftRingHom (polynomialExpansion K)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (polynomialExpansion_injective K))

@[simp] theorem coefficientExpansion_polynomial (P : K[X]) :
    coefficientExpansion K (algebraMap K[X] (RatFunc K) P) =
      polynomialExpansion K P := by
  exact RatFunc.liftRingHom_algebraMap _ _ _

theorem coefficientExpansion_div (P Q : K[X]) :
    coefficientExpansion K
      (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) =
      polynomialExpansion K P / polynomialExpansion K Q := by
  rw [map_div₀, coefficientExpansion_polynomial, coefficientExpansion_polynomial]

/-- Every nonzero rational coefficient retains a nonzero Laurent expansion. -/
theorem coefficientExpansion_injective : Function.Injective (coefficientExpansion K) :=
  (coefficientExpansion K).injective

namespace Rational

open LevelSixRationalSections

/-- Framed expansion of rational sections at the actual eta cusp. -/
def expansion (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    SectionRing K →+* LaurentSeries K :=
  eval₂RingHom (coefficientExpansion K)
    (↑(etaRealization K h6 r hr).change.u⁻¹ : LaurentSeries K)

theorem expansion_sectionOf (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (k : ℕ) (f : RatFunc K) :
    expansion K h6 r hr (sectionOf k f) = coefficientExpansion K f *
      (↑(etaRealization K h6 r hr).change.u⁻¹ : LaurentSeries K) ^ k := by
  simp [expansion, sectionOf]

/-- Injectivity holds on each fixed weight; the mixed-weight map is not
claimed injective. The actual differential frame is a unit. -/
theorem expansion_injective_weight (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (k : ℕ) (F G : SectionRing K) (hF : IsWeight k F) (hG : IsWeight k G)
    (h : expansion K h6 r hr F = expansion K h6 r hr G) : F = G := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  rw [expansion_sectionOf, expansion_sectionOf] at h
  have hw : (↑(etaRealization K h6 r hr).change.u⁻¹ : LaurentSeries K) ^ k ≠ 0 :=
    pow_ne_zero _ (Units.ne_zero _)
  exact congrArg (sectionOf k) ((coefficientExpansion K).injective (mul_right_cancel₀ hw h))

theorem expansion_ofPolynomial_sectionOf
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) (k : ℕ) (f : K[X]) :
    expansion K h6 r hr (ofPolynomial (LevelSixModularSections.sectionOf k f)) =
      (etaRealization K h6 r hr).expansion (LevelSixModularSections.sectionOf k f) := by
  rw [ofPolynomial_sectionOf, expansion_sectionOf, coefficientExpansion_polynomial,
    LevelSixTateSections.TateRealization.expansion_sectionOf,
    etaRealization_base, etaRealization_parameter]
  rfl

/-- Polynomial inclusion preserves the original actual Tate expansion. -/
theorem expansion_ofPolynomial
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (F : LevelSixModularSections.SectionRing K) :
    expansion K h6 r hr (ofPolynomial F) = (etaRealization K h6 r hr).expansion F := by
  induction F using Polynomial.induction_on' with
  | add F G hF hG => simp only [map_add, hF, hG]
  | monomial k f => exact expansion_ofPolynomial_sectionOf K h6 r hr k f

/-- Any polynomial denominator can be used for expansion. For a genuine
fraction use `polynomialExpansion_ne_zero` with its nonzero denominator. -/
theorem expansion_fraction (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (k : ℕ) (P Q : K[X]) :
    expansion K h6 r hr (sectionOf k
      (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q)) =
      (etaRealization K h6 r hr).expansion
        (LevelSixModularSections.sectionOf k P) / polynomialExpansion K Q := by
  rw [expansion_sectionOf, coefficientExpansion_div,
    LevelSixTateSections.TateRealization.expansion_sectionOf,
    etaRealization_base, etaRealization_parameter]
  change polynomialExpansion K P / polynomialExpansion K Q * _ =
    polynomialExpansion K P * _ / polynomialExpansion K Q
  ring

/-- Rational expansion as a quotient with the canonical nonzero denominator. -/
theorem expansion_quotient (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (k : ℕ) (f : RatFunc K) :
    expansion K h6 r hr (sectionOf k f) =
      (etaRealization K h6 r hr).expansion
        (LevelSixModularSections.sectionOf k f.num) /
          polynomialExpansion K f.denom := by
  rw [expansion_sectionOf, coefficientExpansion, RatFunc.liftRingHom_apply,
    LevelSixTateSections.TateRealization.expansion_sectionOf,
    etaRealization_base, etaRealization_parameter]
  change polynomialExpansion K f.num / polynomialExpansion K f.denom * _ =
    polynomialExpansion K f.num * _ / polynomialExpansion K f.denom
  ring

/-- The Serre Fourier comparison extends to all rational coefficients by
localization. No holomorphy of either the numerator or the quotient at the
cusp is required. Its literature dependencies are exactly the already named
polynomial Tate comparison, not an additional rational comparison premise. -/
theorem expansion_serre (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (k : ℕ) (f : RatFunc K) :
    expansion K h6 r hr (sectionOf (k + 2) (serre k f)) =
      theta K (expansion K h6 r hr (sectionOf k f)) -
        (k : LaurentSeries K) / 12 * eisensteinTwo K *
          expansion K h6 r hr (sectionOf k f) := by
  let T := etaRealization K h6 r hr
  let w : LaurentSeries K := ↑T.change.u⁻¹
  let A := polynomialExpansion K f.num
  let B := polynomialExpansion K f.denom
  let DN := polynomialExpansion K (LevelSixModularSections.serre k f.num)
  let DB := polynomialExpansion K (LevelSixModularSections.serre 0 f.denom)
  have hB : B ≠ 0 := polynomialExpansion_ne_zero K f.denom (RatFunc.denom_ne_zero f)
  have hn := LevelSixSerreExpansion.expansion_serre h6 T
    (etaRealization_base K h6 r hr)
    (by simpa only [T, etaRealization_parameter] using eta_eval_discriminant_ne_zero K h6)
    k f.num
  have hd := LevelSixSerreExpansion.expansion_serre h6 T
    (etaRealization_base K h6 r hr)
    (by simpa only [T, etaRealization_parameter] using eta_eval_discriminant_ne_zero K h6)
    0 f.denom
  simp only [LevelSixTateSections.TateRealization.expansion_sectionOf,
    T, etaRealization_base, etaRealization_parameter] at hn hd
  change DN * w ^ (k + 2) = theta K (A * w ^ k) -
    (k : LaurentSeries K) / 12 * eisensteinTwo K * (A * w ^ k) at hn
  simp only [Nat.zero_add, Nat.cast_zero, zero_div, zero_mul, pow_zero, mul_one,
    sub_zero] at hd
  change DB * w ^ 2 = theta K B at hd
  rw [expansion_sectionOf, serre, map_sub, map_div₀, map_div₀,
    coefficientExpansion_polynomial, coefficientExpansion_polynomial,
    coefficientExpansion_polynomial, map_pow, coefficientExpansion_polynomial,
    map_mul, expansion_quotient]
  rw [LevelSixTateSections.TateRealization.expansion_sectionOf,
    etaRealization_base, etaRealization_parameter]
  change (DN / B - A * DB / B ^ 2) * w ^ (k + 2) =
    theta K (A * w ^ k / B) - (k : LaurentSeries K) / 12 * eisensteinTwo K *
      (A * w ^ k / B)
  rw [theta_div K _ _ hB, ← hd]
  have hn' := hn
  rw [pow_add] at hn' ⊢
  field_simp [hB] at hn' ⊢
  linear_combination B * hn'

/-- Fourier comparison on an arbitrary homogeneous rational section. -/
theorem expansion_serreSection (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (k : ℕ) (F : SectionRing K) (hF : IsWeight k F) :
    expansion K h6 r hr (serreSection k F) =
      theta K (expansion K h6 r hr F) -
        (k : LaurentSeries K) / 12 * eisensteinTwo K * expansion K h6 r hr F := by
  obtain ⟨f, rfl⟩ := hF
  rw [serreSection_sectionOf]
  exact expansion_serre K h6 r hr k f

/-- The rational model contains the same Hasse section, with the same frame
and normalized expansion. This is not a new Hasse comparison premise. -/
theorem expansion_hasse (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 3 < p)
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    expansion K h6 r hr (ofPolynomial (LevelSixHasseGeometry.hasseSection p)) = 1 := by
  rw [expansion_ofPolynomial]
  exact eta_expansion_hasse K p hp h6 r hr

/-- The embedded section `12 D H` has expansion `E₂` in characteristic `p`.
The Hasse and Serre laws share the original actual differential frame. -/
theorem expansion_serreHasse (p : ℕ) [Fact p.Prime] [CharP K p] (hp : 3 < p)
    (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    expansion K h6 r hr (ofPolynomial (LevelSixHasseGeometry.serreHasseSection p)) =
      eisensteinTwo K := by
  rw [expansion_ofPolynomial]
  exact eta_expansion_serreHasse K p hp h6 r hr

end Rational

end SptClassification.LevelSixTateInjectivity
