/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartPolynomials
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Degree bounds for principal-part elimination

Triangular elimination never increases the degree of the polynomial used to
realize a prescribed pole. These bounds specialize the full Fourier comparison
to the H and K families in [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

/-- Triangular principal-part elimination preserves the original degree bound. -/
theorem natDegree_principalPartPolynomial_le (raw : ℕ → ℤ → ℤ) (n : ℕ) :
    (principalPartPolynomial raw n).natDegree ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [principalPartPolynomial_eq]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp only [Polynomial.natDegree_X_pow, le_refl]
    · apply Polynomial.natDegree_sum_le_of_forall_le
      intro k _
      have hk : (k : ℕ) < n := Finset.mem_range.mp k.property
      exact (Polynomial.natDegree_C_mul_le _ _).trans ((ih k hk).trans hk.le)

/-- The H polynomial needs no pole larger than its prescribed principal index. -/
theorem natDegree_integralHPolynomial_le (d : ℕ) (a : ℤ) :
    (integralHPolynomial d a).natDegree ≤ principalIndex d := by
  rw [integralHPolynomial_eq, etaPrincipalPolynomial_eq]
  apply (Polynomial.natDegree_sub_le _ _).trans
  exact max_le (natDegree_principalPartPolynomial_le _ _) (by simp)

/-- The K polynomial uses one fewer power of j because the derivative has a pole. -/
theorem natDegree_integralKPolynomial_le (d : ℕ) :
    (integralKPolynomial d).natDegree ≤ principalIndex d - 1 :=
  by
    rw [integralKPolynomial_eq, etaThetaPrincipalPolynomial_eq]
    exact natDegree_principalPartPolynomial_le _ _

end SptClassification.QSeries
