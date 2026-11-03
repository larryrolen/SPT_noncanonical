/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixRationalEvaluation
public import SptClassification.ModularForms.LevelSixTateInjectivity
public import SptClassification.ModularForms.LevelSixEtaFrame
import all SptClassification.ModularForms.LevelSixTateInjectivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Rational sections obtained by eta pole clearing

The polynomial numerator belongs to a holomorphic form of weight `96*h+4`.
Dividing by `(AB)^2 Δ^(8*h)` leaves weight four. This module constructs the
rational section for any numerator; it does not assert that an actual CM form
has such a numerator. The normalization uses the existing frame square
`-b²/12`, so the rational coefficient is `144 P / ((AB)^2 Deta^(8*h))`.
-/

public noncomputable section

namespace SptClassification.LevelSixRationalEtaClearing

open Polynomial LevelSixRationalSections LevelSixRationalEvaluation
  LevelSixTateInjectivity LevelSixTateComparison LevelSixSerreExpansion
  LevelSixEtaFrame

variable {R : Type*} [CommRing R]

/-- The cusp divisor polynomial in the manuscript's coordinate `t=72/t₆`;
[maier2009], Tables 2 and 4, after this coordinate change. -/
def etaDiscriminant : R[X] := X ^ 6 * (X + 8) ^ 2 * (X + 9) ^ 3

/-- The denominator remaining after cancellation of the eta frame powers. -/
def clearingDenominator (h : ℕ) (A B : R[X]) : R[X] :=
  (A * B) ^ 2 * etaDiscriminant ^ (8 * h)

@[simp] theorem map_etaDiscriminant {S : Type*} [CommRing S] (φ : R →+* S) :
    (etaDiscriminant : R[X]).map φ = etaDiscriminant := by
  simp [etaDiscriminant]

@[simp] theorem map_clearingDenominator {S : Type*} [CommRing S] (φ : R →+* S)
    (h : ℕ) (A B : R[X]) :
    (clearingDenominator h A B).map φ = clearingDenominator h (A.map φ) (B.map φ) := by
  simp [clearingDenominator]

/-- Exact integral normalization of the Weierstrass discriminant. -/
theorem curve_discriminant :
    (LevelSixWeierstrass.curve (X : R[X])).Δ = 12 ^ 6 * etaDiscriminant := by
  rw [LevelSixWeierstrass.curve_discriminant]
  simp only [etaDiscriminant]
  ring

variable {K : Type*} [Field K]

/-- Weight-four coefficient in the fixed invariant differential frame. -/
def coefficient (h : ℕ) (A B P : K[X]) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (144 * P) /
    algebraMap K[X] (RatFunc K) (clearingDenominator h A B)

/-- The rational weight-four section attached to a pole-cleared numerator. -/
def rationalSection (h : ℕ) (A B P : K[X]) : SectionRing K :=
  sectionOf 4 (coefficient h A B P)

theorem section_weight (h : ℕ) (A B P : K[X]) : IsWeight 4 (rationalSection h A B P) :=
  ⟨coefficient h A B P, rfl⟩

@[simp] theorem section_coeff (h : ℕ) (A B P : K[X]) :
    (rationalSection h A B P).coeff 4 = coefficient h A B P := by
  exact coeff_sectionOf _ _

theorem etaDiscriminant_eval_ne_zero (x : K) (hx : LevelSixHasseGeometry.IsInterior x) :
    (etaDiscriminant : K[X]).eval x ≠ 0 := by
  rw [LevelSixHasseGeometry.isInterior_iff] at hx
  have h8 : x + 8 ≠ 0 := by simpa [add_eq_zero_iff_eq_neg] using hx.2.1
  have h9 : x + 9 ≠ 0 := by simpa [add_eq_zero_iff_eq_neg] using hx.2.2
  simpa [etaDiscriminant] using
    mul_ne_zero (mul_ne_zero (pow_ne_zero 6 hx.1) (pow_ne_zero 2 h8)) (pow_ne_zero 3 h9)

theorem clearingDenominator_eval_ne_zero (h : ℕ) (A B : K[X]) (x : K)
    (hx : LevelSixHasseGeometry.IsInterior x) (hAB : A.eval x * B.eval x ≠ 0) :
    (clearingDenominator h A B).eval x ≠ 0 := by
  simpa only [clearingDenominator, eval_mul, eval_pow] using
    mul_ne_zero (pow_ne_zero 2 hAB) (pow_ne_zero (8 * h) (etaDiscriminant_eval_ne_zero x hx))

/-- No new interior poles are introduced by eta pole clearing. -/
theorem regularAt_coefficient (h : ℕ) (A B P : K[X]) (x : K)
    (hx : LevelSixHasseGeometry.IsInterior x) (hAB : A.eval x * B.eval x ≠ 0) :
    RegularAt x (coefficient h A B P) :=
  regularAt_fraction x _ _ (clearingDenominator_eval_ne_zero h A B x hx hAB)

/-- The actual Hasse polynomial has no cusp roots. Thus eta clearing leaves
only the explicit CM support as possible poles at its zeros. -/
theorem regularAt_hasse_zero (p : ℕ) [Fact p.Prime] [CharP K p]
    (hp : 3 < p) (h6 : (6 : K) ≠ 0) (h : ℕ) (A B P : K[X]) (x : K)
    (hH : (LevelSixHasseGeometry.H p : K[X]).eval x = 0)
    (hAB : A.eval x * B.eval x ≠ 0) : RegularAt x (coefficient h A B P) :=
  regularAt_coefficient h A B P x
    (LevelSixHasseGeometry.isInterior_of_H_eq_zero p hp h6 x hH) hAB

/-- Point evaluation is justified by the displayed nonvanishing denominator. -/
theorem value_coefficient (h : ℕ) (A B P : K[X]) (x : K)
    (hx : LevelSixHasseGeometry.IsInterior x) (hAB : A.eval x * B.eval x ≠ 0) :
    value x (coefficient h A B P) =
      144 * P.eval x / ((A.eval x * B.eval x) ^ 2 *
        (x ^ 6 * (x + 8) ^ 2 * (x + 9) ^ 3) ^ (8 * h)) := by
  rw [coefficient, value_fraction x _ _
    (clearingDenominator_eval_ne_zero h A B x hx hAB)]
  simp [clearingDenominator, etaDiscriminant]

variable (K)

/-- The actual Tate discriminant, retaining its full power-series expansion. -/
def delta : LaurentSeries K := tateBase K (LevelSixTateSections.tateCurve K).Δ

/-- The Tate equation and the same even frame give `Δ=Deta(t)b^12`.
This uses existing framed Tate comparison inputs, without a new Euler identity
or a new good-reduction assumption. -/
theorem delta_eq_eta (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    delta K = polynomialExpansion K etaDiscriminant * tateBase K (cuspForm K) ^ 12 := by
  have h := congrArg WeierstrassCurve.Δ (etaRealization K h6 r hr).equation
  rw [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ,
    etaRealization_base, etaRealization_parameter, LevelSixWeierstrass.curve_discriminant] at h
  have hw := eta_frame_sq K h6 r hr
  have h12 : (12 : LaurentSeries K) ≠ 0 := by
    have hc := coordinate_coefficient_ne_zero K h6
    intro hz
    apply hc
    rw [hz, zero_mul, zero_mul, zero_mul]
  change _ = delta K at h
  rw [← h]
  change _ = (etaDiscriminant : K[X]).eval₂ (constants K) (etaParameter K) * _
  simp only [etaDiscriminant, eval₂_mul, eval₂_pow, eval₂_X, eval₂_add, eval₂_ofNat]
  have hw12 := congrArg (fun z : LaurentSeries K => z ^ 6) hw
  simp only [← pow_mul] at hw12
  rw [show (2 : ℕ) * 6 = 12 from rfl] at hw12
  rw [hw12]
  field_simp
  <;> ring

/-- True Laurent expansion of the rational section, with its original eta
normalization. Polynomial substitution is injective, so no pole is evaluated
by a fictitious total point-evaluation homomorphism. -/
theorem expansion_section (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (h : ℕ) (A B P : K[X]) :
    Rational.expansion K h6 r hr (rationalSection h A B P) =
      polynomialExpansion K P * tateBase K (cuspForm K) ^ 4 /
        polynomialExpansion K (clearingDenominator h A B) := by
  rw [rationalSection, Rational.expansion_sectionOf, coefficient, coefficientExpansion_div]
  have hw := congrArg (fun z : LaurentSeries K => z ^ 2) (eta_frame_sq K h6 r hr)
  simp only [← pow_mul] at hw
  rw [show (2 : ℕ) * 2 = 4 from rfl] at hw
  rw [hw, map_mul, map_ofNat]
  have h12 : (12 : LaurentSeries K) ≠ 0 := by
    have hc := coordinate_coefficient_ne_zero K h6
    intro hz
    apply hc
    rw [hz, zero_mul, zero_mul, zero_mul]
  field_simp
  <;> ring

/-- The eta cusp form is nonzero as a Laurent series, in the same chart. -/
theorem cuspForm_ne_zero (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    tateBase K (cuspForm K) ≠ 0 := by
  intro hz
  have hw := eta_frame_sq K h6 r hr
  rw [hz, zero_pow (by decide), neg_zero, zero_div] at hw
  exact pow_ne_zero 2 (Units.ne_zero _) hw

/-- The original weight `96*h+4` numerator divided by the actual discriminant
power expands to the constructed weight-four rational section. -/
theorem expansion_cleared_quotient (h6 : (6 : K) ≠ 0) (r : K)
    (hr : r ^ 2 = -12) (h : ℕ) (A B P : K[X]) :
    Rational.expansion K h6 r hr (rationalSection h A B P) =
      (polynomialExpansion K P * tateBase K (cuspForm K) ^ (96 * h + 4)) /
        ((polynomialExpansion K A * polynomialExpansion K B) ^ 2 * delta K ^ (8 * h)) := by
  rw [expansion_section, delta_eq_eta K h6 r hr]
  simp only [clearingDenominator, map_mul, map_pow, mul_pow, pow_add]
  rw [show 96 * h = 12 * (8 * h) by omega,
    pow_mul (tateBase K (cuspForm K)) 12 (8 * h)]
  have hb := pow_ne_zero (8 * h) (pow_ne_zero 12 (cuspForm_ne_zero K h6 r hr))
  exact by
    rw [show (polynomialExpansion K P *
        ((tateBase K (cuspForm K) ^ 12) ^ (8 * h) * tateBase K (cuspForm K) ^ 4)) =
        (polynomialExpansion K P * tateBase K (cuspForm K) ^ 4) *
          (tateBase K (cuspForm K) ^ 12) ^ (8 * h) by ring,
      ← mul_assoc, mul_div_mul_right _ _ hb]

/-- The clearing factor is nonzero for nonzero class polynomials. -/
theorem clearingFactor_ne_zero (h6 : (6 : K) ≠ 0) (r : K)
    (hr : r ^ 2 = -12) (h : ℕ) (A B : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) :
    (polynomialExpansion K A * polynomialExpansion K B) ^ 2 * delta K ^ (8 * h) ≠ 0 := by
  have hd : (etaDiscriminant : K[X]) ≠ 0 := by
    have hn (n : ℕ) : (X + (n : K[X])) ≠ 0 := by
      intro hz
      have hc := congrArg (fun Q : K[X] => Q.coeff 1) hz
      simpa using hc
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 6 X_ne_zero)
      (pow_ne_zero 2 (hn 8))) (pow_ne_zero 3 (hn 9))
  rw [delta_eq_eta K h6 r hr]
  exact mul_ne_zero
    (pow_ne_zero 2 (mul_ne_zero (polynomialExpansion_ne_zero K A hA)
      (polynomialExpansion_ne_zero K B hB)))
    (pow_ne_zero (8 * h) (mul_ne_zero (polynomialExpansion_ne_zero K _ hd)
      (pow_ne_zero 12 (cuspForm_ne_zero K h6 r hr))))

/-- A pole-cleared Laurent identity identifies the original series with the
constructed section. The identity is a numerator representation, not a
regularity or Hasse-vanishing assumption. -/
theorem expansion_eq_of_cleared_identity (h6 : (6 : K) ≠ 0) (r : K)
    (hr : r ^ 2 = -12) (h : ℕ) (A B P : K[X]) (hA : A ≠ 0) (hB : B ≠ 0)
    (F : LaurentSeries K)
    (hF : ((polynomialExpansion K A * polynomialExpansion K B) ^ 2 *
      delta K ^ (8 * h)) * F =
        polynomialExpansion K P * tateBase K (cuspForm K) ^ (96 * h + 4)) :
    Rational.expansion K h6 r hr (rationalSection h A B P) = F := by
  rw [expansion_cleared_quotient, div_eq_iff (clearingFactor_ne_zero K h6 r hr h A B hA hB)]
  simpa only [mul_comm] using hF.symm

end SptClassification.LevelSixRationalEtaClearing
