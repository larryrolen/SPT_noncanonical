/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMFormalProduct
public import SptClassification.ModularForms.HasseObstructionForms

/-!
# The CM product expansion of the conditional logarithmic lift

These equalities identify a weight-two lift's q-expansion with the reduction
of the *same* oriented integral CM product. They use the formal-product/Lambert
deductions and an explicit q-expansion hypothesis. Construction of the lift
and its good-reduction evaluation are separate. See
[rolenManuscript, Section 4, equations (product) and (L)].
-/

public section

namespace SptClassification

open PowerSeries

/-- The q-expansion of a weight-two logarithmic lift equals the
logarithmic derivative of the chosen oriented CM quotient after reduction.
The existence and weight of the lift remain explicit in `I`.
[rolenManuscript, Section 4, equations (product) and (L)] -/
theorem HomogeneousHasseInput.logarithmic_qexp_eq_reduced_cm_product
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F : Type*} [CommRing F] [Algebra (ZMod p) F]
    (I : HomogeneousHasseInput p d F)
    (L : F) (hLq : I.qexp L = QSeries.principalLogarithmicLambertSeries p d)
    (hp6 : ¬p ∣ 6) (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    I.qexp L =
      QSeries.eulerDerivative
          (PowerSeries.map (cmCoefficientReduction p hp6)
            (cmFormalBorcherdsQuotient d hd hsq hmod)) *
        (PowerSeries.map (cmCoefficientReduction p hp6)
          (cmFormalBorcherdsQuotient d hd hsq hmod)).invOfUnit 1 := by
  rw [hLq]
  exact (cmFormalBorcherdsQuotient_reduced_logarithmicLambert
    p d hp6 hd hsq hmod).symm

/-- The q-expansion of the logarithmic lift satisfies the exact
reversed-polynomial numerator equation for the same chosen integral models.
This is the cusp-series consequence needed before a geometric evaluation
identity can be proved. [rolenManuscript, Section 4, equation (L)] -/
theorem HomogeneousHasseInput.logarithmic_qexp_reversed_cm_numerator
    {p d : ℕ} [Fact p.Prime] [Fact (-(d : ℤ) < 0)]
    {F : Type*} [CommRing F] [Algebra (ZMod p) F]
    (I : HomogeneousHasseInput p d F)
    (L : F) (hLq : I.qexp L = QSeries.principalLogarithmicLambertSeries p d)
    (hp6 : ¬p ∣ 6) (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) :
    let models := integralCMClassPolynomials d hd hsq hmod
    I.qexp L *
        PowerSeries.map (cmCoefficientReduction p hp6)
          (cmReversedPolynomialEval models.modelA) *
        PowerSeries.map (cmCoefficientReduction p hp6)
          (cmReversedPolynomialEval models.modelB) =
      QSeries.eulerDerivative
          (PowerSeries.map (cmCoefficientReduction p hp6)
            (cmReversedPolynomialEval models.modelA)) *
        PowerSeries.map (cmCoefficientReduction p hp6)
          (cmReversedPolynomialEval models.modelB) -
      PowerSeries.map (cmCoefficientReduction p hp6)
          (cmReversedPolynomialEval models.modelA) *
        QSeries.eulerDerivative
          (PowerSeries.map (cmCoefficientReduction p hp6)
            (cmReversedPolynomialEval models.modelB)) := by
  rw [hLq]
  exact cmFormalBorcherdsLambert_reversedPolynomialIdentity_mod
    p d hp6 hd hsq hmod

end SptClassification
