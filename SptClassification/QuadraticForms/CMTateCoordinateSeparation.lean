/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMCoordinateSeparation
public import SptClassification.QuadraticForms.LevelSixModuliCoordinate

/-!
# CM separation with the constructed level-six coordinate

The injective coordinate is now a construction on actual geometric marked
pairs. Only individual CM specialization and its compatibility with the fixed
integral eta-value reduction remain inputs to the manuscript deduction.
-/

public section

namespace SptClassification.CMIntegralValues

/-- Away from six, the constructed marked-pair coordinate is available on the
geometric residue field. -/
theorem six_ne_zero_residue (p : ℕ) [Fact p.Prime] (hp6 : ¬p ∣ 6) :
    (6 : AlgebraicClosure (ZMod p)) ≠ 0 := by
  change ((6 : ℕ) : AlgebraicClosure (ZMod p)) ≠ 0
  exact fun h => hp6 ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p 6).mp h)

/-- All-prime polynomial separation with the coordinate-injectivity input
discharged by Tate normalization. The compatibility assumption identifies the
constructed geometric coordinate with the actual eta value under the fixed
residue map; it does not assume a common-pair or separation conclusion. -/
theorem isCoprime_of_tate_specializations
    (d p : ℕ) [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    [DecidableEq (AlgebraicClosure (ZMod p))]
    (hp6 : ¬p ∣ 6) (hp : 3 < p) (hmod : d % 24 = 23)
    (hbound : (d + 1) ^ 2 < 24 * p)
    (models : IntegralCMClassPolynomials d)
    (specialize : ∀ {r : ZMod 12} (Q : LevelSixForm (-(d : ℤ)) r)
      (hodd : Q.b % 2 = 1), Q.Specialization hodd (AlgebraicClosure (ZMod p)))
    (compatible : ∀ {r : ZMod 12} (Q : LevelSixForm (-(d : ℤ)) r)
      (hodd : Q.b % 2 = 1) (v : Ring),
      complexEmbedding v = levelSixEtaQuotient Q.cmPoint →
      LevelSixPair.moduliCoordinate (six_ne_zero_residue p hp6)
        (specialize Q hodd).moduliClass = reduction p hp6 v) :
    IsCoprime (models.modelA.map (cmCoefficientReduction p hp6))
      (models.modelB.map (cmCoefficientReduction p hp6)) := by
  exact isCoprime_of_specializations d p hp6 hp hmod hbound models
    (LevelSixPair.moduliCoordinate (six_ne_zero_residue p hp6))
    (LevelSixPair.moduliCoordinate_injective (six_ne_zero_residue p hp6))
    specialize compatible

end SptClassification.CMIntegralValues
