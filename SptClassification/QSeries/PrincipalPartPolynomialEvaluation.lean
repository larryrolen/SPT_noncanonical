/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalPartPolynomialCore
public import SptClassification.QSeries.ConvergentPowers

/-!
# Convergent evaluation after clearing polynomial poles

Finite Cauchy products evaluate the full integral coefficient rows used in
[rolenManuscript, §3]. All sums here are unconditional sums; over `ℂ` they
are absolutely convergent.
-/

public section

namespace SptClassification.QSeries

/-- A constant integral series has its constant as analytic sum. -/
theorem hasSum_coefficientTerm_C (c : ℤ) (q : ℂ) :
    HasSum (fun n => ((PowerSeries.C c).coeff n : ℂ) * q ^ n) (c : ℂ) := by
  simp only [PowerSeries.coeff_C, Int.cast_ite, Int.cast_zero, ite_mul, zero_mul]
  simpa +contextual using hasSum_ite_eq (0 : ℕ) (c : ℂ)

/-- A power of the formal variable evaluates to the same power of the nome. -/
theorem hasSum_coefficientTerm_X_pow (q : ℂ) (k : ℕ) :
    HasSum (fun n => ((PowerSeries.X ^ k : PowerSeries ℤ).coeff n : ℂ) * q ^ n)
      (q ^ k) := by
  simpa +contextual [PowerSeries.coeff_X_pow] using hasSum_ite_eq k (q ^ k)

/-- Each summand of the cleared polynomial core has its expected analytic value. -/
theorem hasSum_coefficientTerm_clearedRow (U J : PowerSeries ℤ) (q u v : ℂ)
    (hU : HasSum (fun n => (U.coeff n : ℂ) * q ^ n) u)
    (hJ : HasSum (fun n => (J.coeff n : ℂ) * q ^ n) v) (c : ℤ) (k i : ℕ) :
    HasSum (fun n =>
      ((PowerSeries.C c * (PowerSeries.X ^ k * (U * J ^ i))).coeff n : ℂ) * q ^ n)
      ((c : ℂ) * (q ^ k * (u * v ^ i))) := by
  have hp := hasSum_coefficientTerm_pow J q v i hJ
  have hr := hasSum_coefficientTerm_mul U (J ^ i) q u (v ^ i)
    hU.summable.norm hp.summable.norm hU hp
  have hx := hasSum_coefficientTerm_X_pow q k
  have hs := hasSum_coefficientTerm_mul (PowerSeries.X ^ k) (U * J ^ i) q
    (q ^ k) (u * v ^ i) hx.summable.norm hr.summable.norm hx hr
  have hc := hasSum_coefficientTerm_C c q
  exact hasSum_coefficientTerm_mul _ _ _ _ _ hc.summable.norm hs.summable.norm hc hs

/-- Evaluate the cleared integral core as a polynomial in the meromorphic ratio. -/
theorem hasSum_principalPolynomialCore (U J : PowerSeries ℤ) (P : Polynomial ℤ)
    (M : ℕ) (hM : P.natDegree ≤ M) (q u v : ℂ) (hq : q ≠ 0)
    (hU : HasSum (fun n => (U.coeff n : ℂ) * q ^ n) u)
    (hJ : HasSum (fun n => (J.coeff n : ℂ) * q ^ n) v) :
    HasSum (fun n => ((principalPolynomialCore U J M P).coeff n : ℂ) * q ^ n)
      (u * q ^ M * P.eval₂ (Int.castRingHom ℂ) (v / q)) := by
  have hs := hasSum_sum (s := P.support) (fun i _ =>
    hasSum_coefficientTerm_clearedRow U J q u v hU hJ (P.coeff i) (M - i) i)
  have he : (∑ i ∈ P.support, (P.coeff i : ℂ) * (q ^ (M - i) * (u * v ^ i))) =
      u * q ^ M * P.eval₂ (Int.castRingHom ℂ) (v / q) := by
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hiM : i ≤ M := (Polynomial.le_natDegree_of_mem_supp i hi).trans hM
    have hp : q ^ M = q ^ (M - i) * q ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hiM]
    change (P.coeff i : ℂ) * (q ^ (M - i) * (u * v ^ i)) =
      u * q ^ M * ((P.coeff i : ℂ) * (v / q) ^ i)
    rw [hp, div_pow]
    field_simp
  rw [he] at hs
  simpa only [coeff_principalPolynomialCore_sum, Int.cast_sum,
    Finset.sum_mul] using hs

/-- The complete Laurent row has the analytic sum of its eta-polynomial expression. -/
theorem hasSum_polynomialRows_etaJRow (U J : PowerSeries ℤ) (P : Polynomial ℤ)
    (M : ℕ) (hM : P.natDegree ≤ M) (q u v : ℂ) (hq : q ≠ 0)
    (hU : HasSum (fun n => (U.coeff n : ℂ) * q ^ n) u)
    (hJ : HasSum (fun n => (J.coeff n : ℂ) * q ^ n) v) :
    HasSum (fun n : ℕ => (polynomialRows (etaJRow U J) P ((M : ℤ) - (n : ℤ)) : ℂ) * q ^ n)
      (u * q ^ M * P.eval₂ (Int.castRingHom ℂ) (v / q)) := by
  simpa only [coeff_principalPolynomialCore U J P M hM] using
    hasSum_principalPolynomialCore U J P M hM q u v hq hU hJ

/-- Absolute convergence includes the entire positive tail of the Laurent row. -/
theorem summable_norm_polynomialRows_etaJRow (U J : PowerSeries ℤ) (P : Polynomial ℤ)
    (M : ℕ) (hM : P.natDegree ≤ M) (q u v : ℂ) (hq : q ≠ 0)
    (hU : HasSum (fun n => (U.coeff n : ℂ) * q ^ n) u)
    (hJ : HasSum (fun n => (J.coeff n : ℂ) * q ^ n) v) :
    Summable (fun n : ℕ => ‖(polynomialRows (etaJRow U J) P ((M : ℤ) - (n : ℤ)) : ℂ) * q ^ n‖) :=
  (hasSum_polynomialRows_etaJRow U J P M hM q u v hq hU hJ).summable.norm

end SptClassification.QSeries
