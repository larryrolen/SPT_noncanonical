/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.ClassicalWeierstrassCoefficients
public import SptClassification.QuadraticForms.CMMarkedEtaModel

/-!
# Marked eta identification and CM action from classical literature

The classical coefficient premises in `ClassicalWeierstrassCoefficients`
complete the analytic input to the proved marked-coordinate argument.
These results retain those visible literature admissions in their dependency
cones. They construct a complex CM action, not its reduction at a prime.
-/

public section

namespace SptClassification

open ComplexUniformization LevelSixWeierstrass

namespace ComplexUniformization

/-- The positive real square root, viewed as a complex number, squares to three. -/
theorem complex_sqrt_three_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

/-- The actual lattice marking has the eta parameter, conditional only on the
named classical literature premises used in the construction. -/
theorem upperHalfPlanePair_tateCoordinate_eq_eta (z : UpperHalfPlane) :
    LevelSixPair.tateCoordinate (by norm_num) (upperHalfPlanePair z) =
      tateParameter (levelSixEtaQuotient z) := by
  exact upperHalfPlanePair_tateCoordinate_eq_eta_of_analytic_data
    analyticOnNhd_markedShortA_literature analyticOnNhd_markedShortX_literature
    analyticOnNhd_markedShortY_literature Real.pi (Real.sqrt 3)
    (by exact_mod_cast Real.pi_ne_zero) complex_sqrt_three_sq
    tendsto_markedShortA_literature tendsto_markedShortX_literature
    tendsto_markedShortY_literature z

end ComplexUniformization

namespace LevelSixForm

variable {D : ℤ} {s : ZMod 12} [Fact (D < 0)] (Q : LevelSixForm D s)

/-- A rational equivalence from the actual CM cubic to its eta model preserving
the specified six-torsion generator. -/
theorem exists_pointed_eta_equiv :
    ∃ e : RationalPointMap.CurveEquiv Q.complexPair.curve
      (pair (levelSixEtaQuotient Q.cmPoint)
        (eta_discriminant_ne_zero Q.cmPoint)).curve,
      e.toAddEquiv Q.complexPair.point =
        (pair (levelSixEtaQuotient Q.cmPoint)
          (eta_discriminant_ne_zero Q.cmPoint)).point := by
  exact Q.exists_pointed_eta_equiv_of_analytic_data
    analyticOnNhd_markedShortA_literature analyticOnNhd_markedShortX_literature
    analyticOnNhd_markedShortY_literature Real.pi (Real.sqrt 3)
    (by exact_mod_cast Real.pi_ne_zero) complex_sqrt_three_sq
    tendsto_markedShortA_literature tendsto_markedShortX_literature
    tendsto_markedShortY_literature

/-- The actual eta fiber carries the rational CM generator with its quadratic
relation and orientation scalar. The deduction uses classical analytic
literature; algebraic descent and compatible specialization remain separate. -/
theorem exists_eta_CM_action (hodd : Q.b % 2 = 1)
    (n : ℕ) (hn : 4 * (n : ℤ) = 1 - D) :
    ∃ a : RationalPointMap.endomorphismRing
        (LevelSixWeierstrass.curve (levelSixEtaQuotient Q.cmPoint)),
      a * a - a + (n : RationalPointMap.endomorphismRing
        (LevelSixWeierstrass.curve (levelSixEtaQuotient Q.cmPoint))) = 0 ∧
      RationalPointMap.pointAction _ a
        (sixPoint (levelSixEtaQuotient Q.cmPoint) (eta_discriminant_ne_zero Q.cmPoint)) =
        ((Q.b + 1) / 2 : ℤ) •
          sixPoint (levelSixEtaQuotient Q.cmPoint) (eta_discriminant_ne_zero Q.cmPoint) ∧
      ∀ m : ℤ, a ≠ m := by
  exact Q.exists_eta_CM_action_of_analytic_data
    analyticOnNhd_markedShortA_literature analyticOnNhd_markedShortX_literature
    analyticOnNhd_markedShortY_literature Real.pi (Real.sqrt 3)
    (by exact_mod_cast Real.pi_ne_zero) complex_sqrt_three_sq
    tendsto_markedShortA_literature tendsto_markedShortX_literature
    tendsto_markedShortY_literature hodd n hn

end LevelSixForm

end SptClassification
