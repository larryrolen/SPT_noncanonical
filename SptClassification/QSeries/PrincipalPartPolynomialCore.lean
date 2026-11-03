/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartPolynomials
public import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# Clearing the poles of integral eta polynomials

A polynomial combination of the Laurent rows has an ordinary integral power
series after multiplying by a sufficiently large power of the nome. The
coefficient identity includes the entire positive tail [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

/-- Expand a polynomial combination of rows over its finite support. -/
theorem polynomialRows_eq_sum (raw : ℕ → ℤ → ℤ) (P : Polynomial ℤ) (k : ℤ) :
    polynomialRows raw P k = ∑ i ∈ P.support, P.coeff i * raw i k := by
  nth_rw 1 [← Polynomial.sum_C_mul_X_pow_eq P]
  simp only [Polynomial.sum_def, map_sum, polynomialRows_C_mul,
    polynomialRows_X_pow, Finset.sum_apply, zsmul_eq_mul, Pi.mul_apply,
    Pi.intCast_apply, Int.cast_id]

/-- Shifting to a larger common pole gives precisely the original Laurent row. -/
theorem coeff_X_pow_mul_eq_shiftedPrincipalRow (F : PowerSeries ℤ)
    (i M m : ℕ) (hi : i ≤ M) :
    (PowerSeries.X ^ (M - i) * F).coeff m =
      shiftedPrincipalRow F i ((M : ℤ) - (m : ℤ)) := by
  rw [PowerSeries.coeff_X_pow_mul', shiftedPrincipalRow_eq]
  split_ifs with h₁ h₂ h₂
  · exact congrArg (fun n => F.coeff n) (by omega)
  · omega
  · omega
  · rfl

/-- The ordinary integral core after clearing a common polynomial pole of order `M`. -/
noncomputable def principalPolynomialCore (U J : PowerSeries ℤ) (M : ℕ)
    (P : Polynomial ℤ) : PowerSeries ℤ :=
  ∑ i ∈ P.support, PowerSeries.C (P.coeff i) *
    (PowerSeries.X ^ (M - i) * (U * J ^ i))

theorem principalPolynomialCore_eq (U J : PowerSeries ℤ) (M : ℕ)
    (P : Polynomial ℤ) :
    principalPolynomialCore U J M P =
      ∑ i ∈ P.support, PowerSeries.C (P.coeff i) *
        (PowerSeries.X ^ (M - i) * (U * J ^ i)) := (rfl)

theorem coeff_principalPolynomialCore_sum (U J : PowerSeries ℤ)
    (M : ℕ) (P : Polynomial ℤ) (m : ℕ) :
    (principalPolynomialCore U J M P).coeff m =
      ∑ i ∈ P.support,
        (PowerSeries.C (P.coeff i) *
          (PowerSeries.X ^ (M - i) * (U * J ^ i))).coeff m := by
  simp only [principalPolynomialCore, map_sum]

/-- The cleared power series recovers every coefficient of the full Laurent row. -/
theorem coeff_principalPolynomialCore (U J : PowerSeries ℤ) (P : Polynomial ℤ)
    (M : ℕ) (hM : P.natDegree ≤ M) (m : ℕ) :
    (principalPolynomialCore U J M P).coeff m =
      polynomialRows (etaJRow U J) P ((M : ℤ) - (m : ℤ)) := by
  rw [principalPolynomialCore_eq, map_sum, polynomialRows_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq_shiftedPrincipalRow]
  · rw [etaJRow_eq]
  · exact (Polynomial.le_natDegree_of_mem_supp i hi).trans hM

/-- A polynomial row has no coefficients above any chosen upper bound for its degree. -/
theorem polynomialRows_etaJRow_above (U J : PowerSeries ℤ) (P : Polynomial ℤ)
    (M : ℕ) (hM : P.natDegree ≤ M) (k : ℤ) (hk : (M : ℤ) < k) :
    polynomialRows (etaJRow U J) P k = 0 := by
  rw [polynomialRows_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hiM : i ≤ M := (Polynomial.le_natDegree_of_mem_supp i hi).trans hM
  simp [etaJRow_eq, shiftedPrincipalRow_eq, show ¬k ≤ (i : ℤ) by omega]

/-- The derivative rows use the same cleared core with a different initial factor. -/
theorem etaThetaJRow_eq_etaJRow (U J : PowerSeries ℤ) :
    etaThetaJRow U J = etaJRow (U * (J - eulerDerivative J)) J := by
  funext n k
  rw [etaThetaJRow_eq, etaJRow_eq]

/-- A derivative-polynomial row vanishes above the degree of its polynomial. -/
theorem polynomialRows_etaThetaJRow_above (U J : PowerSeries ℤ) (P : Polynomial ℤ)
    (M : ℕ) (hM : P.natDegree ≤ M) (k : ℤ) (hk : (M : ℤ) < k) :
    polynomialRows (etaThetaJRow U J) P k = 0 := by
  rw [etaThetaJRow_eq_etaJRow]
  exact polynomialRows_etaJRow_above _ _ P M hM k hk

end SptClassification.QSeries
