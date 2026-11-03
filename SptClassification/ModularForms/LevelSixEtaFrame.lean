/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixTateComparison
import all SptClassification.ModularForms.LevelSixModularSections
import all SptClassification.ModularForms.LevelSixSerreExpansion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The even differential frame at the eta cusp

Maier's weight-one form vanishing at infinity has quadratic character.
Its square identifies the even powers of the existing invariant differential
frame without choosing a square root in the coefficient ring.
-/

public noncomputable section

namespace SptClassification.LevelSixEtaFrame

open LevelSixModularSections LevelSixSerreExpansion LevelSixTateSections
  LevelSixTateComparison

/-- The integral Euler unit in `eta(τ) eta(6τ)^6 / (eta(2τ)^2 eta(3τ)^3)`.
The omitted initial power is exactly `q`; see [maier2009], Table 11, p.31. -/
def cuspFormUnit : PowerSeries ℤ :=
  etaEulerSeries 1 * etaEulerSeries 6 ^ 6 *
    etaMultiplePartitionSeries 2 ^ 2 * etaMultiplePartitionSeries 3 ^ 3

@[simp] theorem cuspFormUnit_constantCoeff :
    PowerSeries.constantCoeff cuspFormUnit = 1 := by
  simp [cuspFormUnit, map_mul, map_pow, etaEulerSeries_constantCoeff,
    etaMultiplePartitionSeries_constantCoeff]

variable (K : Type*) [Field K]

/-- The actual integral cusp expansion of Maier's alternative weight-one form. -/
def cuspForm : PowerSeries K :=
  PowerSeries.X * PowerSeries.map (Int.castRingHom K) cuspFormUnit

/-- The eta differential identity in the manuscript's coordinate `t=72/t₆`.
This is [maier2009], (6.6), p.29, with the two finite nonzero cusp values
`t₆=-8,-9` (Table 2), and `h₆=t * bar h₆` (Tables 8 and 11).
Inversion of `t₆=72/t` gives the minus sign. The resulting integral Laurent
identity specializes to every coefficient field; no invertibility of six
is needed for this identity itself. The form is the explicit eta product
above, not an unspecified differential frame. -/
theorem eta_parameter_derivative_literature :
    theta K (etaParameter K) =
      -(etaParameter K * (etaParameter K + 8) * (etaParameter K + 9)) *
        tateBase K (cuspForm K) ^ 2 := by
  sorry

/-- The nonzero coefficient of the coordinate derivative in the eta chart. -/
theorem coordinate_coefficient_ne_zero (h6 : (6 : K) ≠ 0) :
    (12 * etaParameter K * (etaParameter K + 8) * (etaParameter K + 9)) ≠ 0 := by
  have h6' : (6 : LaurentSeries K) ≠ 0 := by
    simpa only [map_ofNat, map_zero] using
      (show constants K 6 ≠ constants K 0 from (constants K).injective.ne h6)
  have h0 : etaParameter K ≠ 0 := by
    simpa only [map_zero] using etaParameter_ne_constant K 0
  have h8 : etaParameter K ≠ -8 := by
    simpa only [map_neg, map_ofNat] using etaParameter_ne_constant K (-8)
  have h9 : etaParameter K ≠ -9 := by
    simpa only [map_neg, map_ofNat] using etaParameter_ne_constant K (-9)
  simpa [coordinateDerivative] using
    coordinateDerivative_eval_ne_zero (etaParameter K) h6' h0 h8 h9

/-- Every chosen eta Tate realization has the same square of its frame.
The normalization is `-bar h₆²/12`, including the factor twelve. -/
theorem eta_frame_sq (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12) :
    (↑(etaRealization K h6 r hr).change.u⁻¹ : LaurentSeries K) ^ 2 =
      -(tateBase K (cuspForm K) ^ 2) / 12 := by
  have h := eta_expansion_coordinateSection K h6 r hr
  rw [coordinateSection, TateRealization.expansion_sectionOf,
    etaRealization_base, etaRealization_parameter] at h
  change (coordinateDerivative : Polynomial K).eval₂ (constants K) (etaParameter K) *
    (↑(etaRealization K h6 r hr).change.u⁻¹ : LaurentSeries K) ^ 2 = _ at h
  simp only [coordinateDerivative, Polynomial.eval₂_mul, Polynomial.eval₂_add,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat] at h
  rw [eta_parameter_derivative_literature] at h
  have hn := coordinate_coefficient_ne_zero K h6
  have h12 : (12 : LaurentSeries K) ≠ 0 := by
    intro hz
    apply hn
    rw [hz, zero_mul, zero_mul, zero_mul]
  apply mul_left_cancel₀ hn
  rw [h]
  field_simp
  <;> ring

/-- Even-weight expansions descend to the explicit square of the eta form.
The polynomial coefficient and its actual Laurent substitution are retained. -/
theorem eta_expansion_even (h6 : (6 : K) ≠ 0) (r : K) (hr : r ^ 2 = -12)
    (m : ℕ) (f : Polynomial K) :
    (etaRealization K h6 r hr).expansion (sectionOf (2 * m) f) =
      f.eval₂ (constants K) (etaParameter K) *
        (-(tateBase K (cuspForm K) ^ 2) / 12) ^ m := by
  rw [TateRealization.expansion_sectionOf, etaRealization_base,
    etaRealization_parameter, pow_mul, eta_frame_sq]
  rfl

end SptClassification.LevelSixEtaFrame
