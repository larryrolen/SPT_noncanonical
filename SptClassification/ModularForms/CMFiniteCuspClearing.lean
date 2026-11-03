/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMActualCuspClearing
public import SptClassification.ModularForms.EtaQuotientCuspsEulerGerms
public import SptClassification.ModularForms.LevelSixFiniteCuspCharts

/-!
# The CM polynomial factor at the finite level-six cusps

The eta coordinate has finite values at zero, one-half and one-third. Its
actual Euler expansions therefore make every polynomial in the coordinate
analytic at these cusps. Together with the infinity cancellation, this is
the local cusp calculation for the clearing factor in
[rolenManuscript, Section 4, paragraph following equation (hasse)].
The slash expansions of the lift and discriminant remain separate inputs.
-/

public section

namespace SptClassification

namespace FiniteLevelSixCusp

/-- The actual analytic eta-coordinate expressions, including the cusp value. -/
noncomputable def coordinate : FiniteLevelSixCusp → ℂ → ℂ
  | .zero, q => 72 * q / levelSixEulerUnit q
  | .half, q => -9 * cuspHalfEulerUnit q
  | .third, q => -8 * cuspThirdEulerUnit q

/-- Finite values of the eta coordinate at the three cusps. -/
def value : FiniteLevelSixCusp → ℂ
  | .zero => 0
  | .half => -9
  | .third => -8

@[simp] theorem coordinate_zero (c : FiniteLevelSixCusp) :
    c.coordinate 0 = c.value := by
  cases c <;> simp [coordinate, value, cuspHalfEulerUnit_zero, cuspThirdEulerUnit_zero]

/-- The chosen chart functions are actual expansions of the eta quotient. -/
theorem coordinate_qParam (c : FiniteLevelSixCusp) (z : UpperHalfPlane) :
    c.coordinate (Function.Periodic.qParam 1 z) =
      levelSixEtaQuotient (c.approach z) := by
  cases c with
  | zero =>
      simp only [coordinate, approach_zero]
      rw [levelSixEtaQuotient_fricke_six, levelSixEtaQuotient_eq_unit_div_qParam]
      simp only [div_div_eq_mul_div]
  | half =>
      simp only [coordinate, approach_half]
      exact (levelSixEtaQuotient_cuspHalf_widthThree z).symm
  | third =>
      simp only [coordinate, approach_third]
      exact (levelSixEtaQuotient_cuspThird_euler z).symm

/-- The eta coordinate is analytic at each finite cusp. -/
theorem analyticAt_coordinate (c : FiniteLevelSixCusp) :
    AnalyticAt ℂ c.coordinate 0 := by
  have hhalf : AnalyticAt ℂ cuspHalfEulerUnit 0 := by
    have h : DifferentiableOn ℂ cuspHalfEulerUnit (Metric.ball 0 1) := by
      intro z hz
      exact (differentiableAt_cuspHalfEulerUnit (by simpa using hz)).differentiableWithinAt
    exact h.analyticAt (Metric.isOpen_ball.mem_nhds (by simp))
  cases c with
  | zero =>
      exact (analyticAt_const.mul analyticAt_id).div
        (analyticAt_levelSixEulerUnit (by simp)) (by simp)
  | half => exact analyticAt_const.mul hhalf
  | third =>
      have hthird : AnalyticAt ℂ cuspThirdEulerUnit 0 := by
        convert hhalf.inv (by simp) using 1
        ext q
        exact cuspThirdEulerUnit_eq q
      exact analyticAt_const.mul hthird

/-- The paired CM polynomial factor evaluated in a finite cusp chart. -/
noncomputable def cmFactor (c : FiniteLevelSixCusp) (D : ℤ) [Fact (D < 0)]
    (q : ℂ) : ℂ :=
  ((cmClassPolynomialA D).eval (c.coordinate q) *
    (cmClassPolynomialB D).eval (c.coordinate q)) ^ 2

/-- Every polynomial in the finite eta coordinate is analytic at the cusp. -/
theorem analyticAt_coordinate_eval (c : FiniteLevelSixCusp) (P : Polynomial ℂ) :
    AnalyticAt ℂ (fun q => P.eval (c.coordinate q)) 0 := by
  have h := Finset.analyticAt_sum (Finset.range (P.natDegree + 1))
    (f := fun i q => P.coeff i * c.coordinate q ^ i)
    (fun i _ => analyticAt_const.mul (c.analyticAt_coordinate.pow i))
  convert h using 1
  ext q
  simp only [Finset.sum_apply, Polynomial.eval_eq_sum_range]

/-- There is no polynomial cusp pole to remove at any finite cusp. -/
theorem analyticAt_cmFactor (c : FiniteLevelSixCusp) (D : ℤ) [Fact (D < 0)] :
    AnalyticAt ℂ (c.cmFactor D) 0 :=
  ((c.analyticAt_coordinate_eval (cmClassPolynomialA D)).mul
    (c.analyticAt_coordinate_eval (cmClassPolynomialB D))).pow 2

/-- On the punctured chart the analytic factor has precisely its original
CM polynomial expression. -/
theorem cmFactor_qParam (c : FiniteLevelSixCusp) (D : ℤ) [Fact (D < 0)]
    (z : UpperHalfPlane) :
    c.cmFactor D (Function.Periodic.qParam 1 z) =
      ((cmClassPolynomialA D).eval (levelSixEtaQuotient (c.approach z)) *
        (cmClassPolynomialB D).eval (levelSixEtaQuotient (c.approach z))) ^ 2 := by
  simp only [cmFactor, coordinate_qParam]

/-- Multiplication by the squared CM factor and any holomorphic discriminant
and lift expansions is analytic at a finite cusp. Here `V` and `J` are the
slash expansions in the same chart; their existence is not asserted. -/
theorem analyticAt_cleared_lift (c : FiniteLevelSixCusp) (D : ℤ) [Fact (D < 0)]
    {V J : ℂ → ℂ} (hV : AnalyticAt ℂ V 0) (hJ : AnalyticAt ℂ J 0) :
    AnalyticAt ℂ (fun q => c.cmFactor D q * V q ^ (8 * formClassNumber D) * J q) 0 :=
  ((c.analyticAt_cmFactor D).mul (hV.pow (8 * formClassNumber D))).mul hJ

end FiniteLevelSixCusp

end SptClassification
