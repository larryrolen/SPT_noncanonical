/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.IntegralClassPolynomials

/-!
# Integral descent of the oriented CM polynomials

The coefficient descent supplied by [rolen2026canonical, Lemma 4.1] and the
proved count of oriented primitive classes give the two degree statements in
the submitted manuscript. The polynomials here specialize to the actual
complex eta-coordinate products.
-/

public section

namespace SptClassification

/-- The submitted manuscript's integral CM polynomial and degree assertion.
The monic coefficient descent is the named literature premise
`integralCMClassPolynomials_literature`; the degree of each actual product is
deduced from its oriented primitive classes. -/
theorem cmClassPolynomialPair_integral_descent (d : ℕ)
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23) :
    letI : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
    ∃ A B : Polynomial (Localization.Away (6 : ℤ)),
      A.Monic ∧ B.Monic ∧
      A.map cmCoefficientComplexMap = cmClassPolynomialA (-(d : ℤ)) ∧
      B.map cmCoefficientComplexMap = cmClassPolynomialB (-(d : ℤ)) ∧
      A.natDegree = 2 * formClassNumber (-(d : ℤ)) ∧
      B.natDegree = 2 * formClassNumber (-(d : ℤ)) := by
  letI : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
  let models := integralCMClassPolynomials d hd hsq hmod
  exact ⟨models.modelA, models.modelB, models.monicA, models.monicB,
    models.complexA, models.complexB, models.degreeA hmod, models.degreeB hmod⟩

end SptClassification
