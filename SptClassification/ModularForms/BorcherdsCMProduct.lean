/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMFormalProduct
public import SptClassification.ModularForms.CMHasseComparison
public import SptClassification.ModularForms.CMLogarithmicLift
public import SptClassification.ModularForms.PrincipalForms

/-!
# The normalized CM Borcherds product at the infinity cusp

The analytic product below is exactly the orientation quotient of the actual
level-six CM class polynomials.  Its exponents are the square-index
coefficients of the prescribed integral form `H_d`.  The near-cusp product
identity is the named literature input [rolen2026canonical, Theorem 4.2,
PDF pp. 6–7].  The reduction and Hasse arguments of
[rolenManuscript, Section 4] are separate obligations.
-/

public section

namespace SptClassification

/-- The partial normalized Borcherds product attached to the actual `H_d`
coefficients. The index starts at one, as in [rolen2026canonical, (4.4)]. -/
noncomputable def cmBorcherdsPartialProduct (d N : ℕ) (q : ℂ) : ℂ :=
  ∏ m ∈ Finset.Icc 1 N,
    (1 - q ^ m) ^
      (characterTwelve (m : ℤ) *
        QSeries.principalHFourier d (QSeries.fFourier d) ((m : ℤ) ^ 2))

/-- Every finite stage has constant value one at the infinity parameter.
This fixes the normalization appearing in [rolen2026canonical, Theorem 4.2]. -/
theorem cmBorcherdsPartialProduct_zero (d N : ℕ) :
    cmBorcherdsPartialProduct d N 0 = 1 := by
  unfold cmBorcherdsPartialProduct
  apply Finset.prod_eq_one
  intro m hm
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  simp [zero_pow (Nat.ne_of_gt hmpos)]

/-- Analytic part of [rolen2026canonical, Theorem 4.2, PDF pp. 6–7].
For squarefree `d ≡ 23 (mod 24)`, the product near `q = 0` converges to
`A_d(t)/B_d(t)`, with the coefficient and orientation normalizations of
the manuscript. The source also asserts an integral formal-series identity;
that stronger assertion is not used here. -/
theorem rolen_cmBorcherdsProduct_near_infinity (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hsq : Squarefree d) (hmod : d % 24 = 23) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : UpperHalfPlane,
      ‖Function.Periodic.qParam 1 z‖ < ε →
        Filter.Tendsto
          (fun N : ℕ => cmBorcherdsPartialProduct d N
            (Function.Periodic.qParam 1 z)) Filter.atTop
          (nhds (cmBorcherdsQuotient (-(d : ℤ)) z)) := by
  sorry

end SptClassification
