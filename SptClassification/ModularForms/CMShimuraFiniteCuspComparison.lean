/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMShimuraFiniteCuspGerm
public import SptClassification.ModularForms.CMFiniteDiscriminantGerm
public import SptClassification.ModularForms.PositiveCuspProducts

/-!
# The pole-cleared principal lift at the finite level-six cusps

The lift, CM polynomial and discriminant germs are independently obtained
from the actual principal Weil input and the three determinant-normalized
charts. Their product is the nome germ of the cleared lift. The separate
comparison with the removable interior extension is made after this local
calculation. [rolenManuscript, Section 4, equations (J) and (hasse)]
-/

public section

namespace SptClassification

namespace FiniteLevelSixCusp

/-- The actual finite-cusp pole-clearing product in the width-one nome. -/
noncomputable def clearedShimuraGerm (c : FiniteLevelSixCusp)
    (D : ℤ) [Fact (D < 0)] (J : ℂ → ℂ) (q : ℂ) : ℂ :=
  c.cmFactor D q * c.discriminantGerm q ^ (8 * formClassNumber D) * J q

/-- The finite-cusp product is holomorphic at the cusp. -/
theorem analyticAt_clearedShimuraGerm (c : FiniteLevelSixCusp)
    (D : ℤ) [Fact (D < 0)] (J : ℂ → ℂ)
    (hJ : AnalyticAt ℂ J 0) :
    AnalyticAt ℂ (c.clearedShimuraGerm D J) 0 := by
  change AnalyticAt ℂ (fun q =>
    c.cmFactor D q * c.discriminantGerm q ^ (8 * formClassNumber D) * J q) 0
  exact c.analyticAt_cleared_lift D c.analyticAt_discriminantGerm hJ

/-- In each determinant-normalized chart the nome product is precisely the
CM polynomial square, the discriminant slash and the weight-four lift slash.
This pointwise equation is used away from removable CM poles. -/
theorem clearedShimuraGerm_qParam (c : FiniteLevelSixCusp)
    (D : ℤ) [Fact (D < 0)] (F J : ℂ → ℂ) (z : UpperHalfPlane)
    (hJ : J (Function.Periodic.qParam 1 z) = c.weightFourSlash F z) :
    c.clearedShimuraGerm D J (Function.Periodic.qParam 1 z) =
      cmPoleFactor D (c.approach z) ^ 2 *
        c.discriminantSlash z ^ (8 * formClassNumber D) *
          c.weightFourSlash F z := by
  rw [clearedShimuraGerm, c.cmFactor_qParam, c.discriminantGerm_qParam, hJ]
  simp only [cmPoleFactor_eq, Polynomial.eval_mul]

/-- The finite nome product is the classical slash of the actual
discriminant-cleared principal lift. The equality concerns the meromorphic
representative; the removable extension is compared by punctured germs. -/
theorem clearedShimuraGerm_qParam_eq_evenWeightSlash (c : FiniteLevelSixCusp)
    (D : ℤ) [Fact (D < 0)] (F J : ℂ → ℂ) (z : UpperHalfPlane)
    (hJ : J (Function.Periodic.qParam 1 z) = c.weightFourSlash F z) :
    c.clearedShimuraGerm D J (Function.Periodic.qParam 1 z) =
      PositiveCuspAction.evenWeightSlash
        (48 * formClassNumber D + 2) c.chartGL
        (fun w : UpperHalfPlane =>
          ModularForm.discriminant w ^ (8 * formClassNumber D) *
            (cmPoleFactor D w ^ 2 * F w)) z := by
  rw [c.clearedShimuraGerm_qParam D F J z hJ]
  have hw : 48 * formClassNumber D + 2 =
      6 * (8 * formClassNumber D) + 2 := by omega
  rw [hw, PositiveCuspAction.evenWeightSlash_clearing]
  rw [← c.discriminantSlash_eq_evenWeightSlash,
    ← c.weightFourSlash_eq_evenWeightSlash, c.chartGL_smul]

end FiniteLevelSixCusp

end SptClassification
