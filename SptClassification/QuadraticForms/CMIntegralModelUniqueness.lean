/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.CMIntegralValues

/-!
# Uniqueness of integral models of the oriented CM products

The coefficient embedding of `ℤ[1/6]` into `ℂ` is injective. Thus the
localized polynomials supplied by [rolen2026canonical, Lemma 4.1] are
determined by the actual oriented complex products, including after reduction.
This fact does not use a reduced elliptic curve or a CM action.
-/

public section

namespace SptClassification

/-- Any two first-pair models of the actual complex CM product coincide. -/
theorem IntegralCMClassPolynomials.modelA_eq
    {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (M N : IntegralCMClassPolynomials d) : M.modelA = N.modelA := by
  apply Polynomial.ext
  intro n
  apply CMIntegralValues.coefficientMap_injective
  have h := congrArg (fun P : Polynomial ℂ => P.coeff n)
    (M.complexA.trans N.complexA.symm)
  simpa only [Polynomial.coeff_map] using h

/-- Any two second-pair models of the actual complex CM product coincide. -/
theorem IntegralCMClassPolynomials.modelB_eq
    {d : ℕ} [Fact (-(d : ℤ) < 0)]
    (M N : IntegralCMClassPolynomials d) : M.modelB = N.modelB := by
  apply Polynomial.ext
  intro n
  apply CMIntegralValues.coefficientMap_injective
  have h := congrArg (fun P : Polynomial ℂ => P.coeff n)
    (M.complexB.trans N.complexB.symm)
  simpa only [Polynomial.coeff_map] using h

/-- A localized descent witness for the actual oriented products is unique,
including its proof fields. -/
instance integralCMClassPolynomials_subsingleton {d : ℕ}
    [Fact (-(d : ℤ) < 0)] : Subsingleton (IntegralCMClassPolynomials d) where
  allEq M N := by
    have hA := M.modelA_eq N
    have hB := M.modelB_eq N
    cases M with
    | mk MA MB hMA hMB hCA hCB =>
      cases N with
      | mk NA NB hNA hNB hNAc hNBc =>
        cases hA
        cases hB
        rfl

/-- The two oriented reductions are independent of which integral descent
witness is used. -/
theorem IntegralCMClassPolynomials.reducedModels_eq
    {d p : ℕ} [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (M N : IntegralCMClassPolynomials d) (hp6 : ¬p ∣ 6) :
    M.modelA.map (cmCoefficientReduction p hp6) =
        N.modelA.map (cmCoefficientReduction p hp6) ∧
      M.modelB.map (cmCoefficientReduction p hp6) =
        N.modelB.map (cmCoefficientReduction p hp6) := by
  constructor
  · rw [M.modelA_eq N]
  · rw [M.modelB_eq N]

end SptClassification
