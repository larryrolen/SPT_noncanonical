/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.LevelSixRationalEvaluation
import all SptClassification.ModularForms.LevelSixRationalEvaluation
import all SptClassification.ModularForms.LevelSixRationalSections
import all SptClassification.ModularForms.LevelSixModularSections
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Laurent expansion of the rational logarithmic section

The weight-two section with coefficient `coordinateDerivative * (A'B-AB')/(AB)`
expands to the logarithmic Euler derivative of the actual eta quotient `A(t)/B(t)`.
The differential frame and eta parameter are the ones used in the Hasse comparison.
[rolenManuscript, Section 4, equations (product) and (L)]
-/

public noncomputable section

namespace SptClassification.LevelSixLogarithmicExpansion

open Polynomial LevelSixRationalSections LevelSixRationalEvaluation
open LevelSixTateInjectivity LevelSixSerreExpansion

variable {K : Type*} [Field K]

/-- The rational logarithmic section in the invariant differential frame. -/
def logarithmicSection (A B : K[X]) : SectionRing K :=
  sectionOf 2 (logarithmicCoefficient A B)

theorem logarithmicSection_weight (A B : K[X]) :
    IsWeight 2 (logarithmicSection A B) := ⟨_, rfl⟩

@[simp] theorem logarithmicSection_coeff (A B : K[X]) :
    (logarithmicSection A B).coeff 2 = logarithmicCoefficient A B := by
  simp [logarithmicSection]

/-- Weight zero removes the Eisenstein correction in the Serre formula. -/
theorem theta_polynomialExpansion (h6 : (6 : K) ≠ 0) (r : K)
    (hr : r ^ 2 = -12) (P : K[X]) :
    theta K (polynomialExpansion K P) =
      polynomialExpansion K (LevelSixModularSections.serre 0 P) *
        (↑(LevelSixTateComparison.etaRealization K h6 r hr).change.u⁻¹ :
          LaurentSeries K) ^ 2 := by
  have h := Rational.expansion_serre K h6 r hr 0
    (algebraMap K[X] (RatFunc K) P)
  simpa only [serre_polynomial, Rational.expansion_sectionOf,
    coefficientExpansion_polynomial, Nat.zero_add, pow_zero, mul_one,
    Nat.cast_zero, zero_div, zero_mul, sub_zero] using h.symm

/-- The actual framed expansion equals the logarithmic derivative of the
actual eta-coordinate quotient. Both polynomials must be nonzero. -/
theorem expansion_logarithmicSection (h6 : (6 : K) ≠ 0) (r : K)
    (hr : r ^ 2 = -12) (A B : K[X]) (hA : A ≠ 0) (hB : B ≠ 0) :
    Rational.expansion K h6 r hr (logarithmicSection A B) =
      theta K (polynomialExpansion K A / polynomialExpansion K B) /
        (polynomialExpansion K A / polynomialExpansion K B) := by
  have ha := polynomialExpansion_ne_zero K A hA
  have hb := polynomialExpansion_ne_zero K B hB
  rw [logarithmicSection, Rational.expansion_sectionOf, logarithmicCoefficient,
    coefficientExpansion_div, theta_div K _ _ hb,
    theta_polynomialExpansion h6 r hr A, theta_polynomialExpansion h6 r hr B]
  simp only [LevelSixModularSections.serre, Nat.cast_zero, C_0,
    zero_mul, add_zero, map_mul, map_sub]
  field_simp [ha, hb]
  <;> ring

end SptClassification.LevelSixLogarithmicExpansion
