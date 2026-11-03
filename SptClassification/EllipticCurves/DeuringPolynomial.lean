/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Deuring polynomials

The integral polynomial `deuringPolynomial n` is the binomial sum
\(\sum_{i=0}^{n}\binom ni^2 X^i\). Its reduction in characteristic
\(2n+1\) is used in the elementary Legendre calculation supporting the
Hasse invariant argument.

For the elliptic-curve context, see [silverman2009, Chapter V]. This module
proves the polynomial identities directly; it does not construct a Hasse section.
-/

public section

namespace SptClassification

open Polynomial

/-- The integral Deuring polynomial, with coefficients `choose n i ^ 2`. -/
@[expose] noncomputable def deuringPolynomial (n : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range (n + 1), monomial i ((n.choose i : ℤ) ^ 2)

/-- The binomial coefficient formula holds at every index, including outside the support. -/
theorem coeff_deuringPolynomial (n k : ℕ) :
    (deuringPolynomial n).coeff k = (n.choose k : ℤ) ^ 2 := by
  classical
  by_cases hk : k ≤ n
  · simp [deuringPolynomial, coeff_monomial, Finset.sum_ite_eq', hk]
  · have hn : n.choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    simp [deuringPolynomial, coeff_monomial, Finset.sum_ite_eq', hk, hn]

/-- The squared binomial recurrence, in the form used for the differential equation. -/
private theorem choose_square_recurrence (n k : ℕ) :
    ((k : ℤ) + 1) ^ 2 * ((n.choose (k + 1) : ℤ) ^ 2) =
      ((n : ℤ) - k) ^ 2 * ((n.choose k : ℤ) ^ 2) := by
  by_cases hk : k ≤ n
  · have hr : (n.choose (k + 1) : ℤ) * ((k : ℤ) + 1) =
        (n.choose k : ℤ) * ((n : ℤ) - k) := by
      have h := Nat.choose_succ_right_eq n k
      exact_mod_cast h
    calc
      ((k : ℤ) + 1) ^ 2 * ((n.choose (k + 1) : ℤ) ^ 2) =
          ((n.choose (k + 1) : ℤ) * ((k : ℤ) + 1)) ^ 2 := by ring
      _ = ((n.choose k : ℤ) * ((n : ℤ) - k)) ^ 2 := congrArg (· ^ 2) hr
      _ = ((n : ℤ) - k) ^ 2 * ((n.choose k : ℤ) ^ 2) := by ring
  · have hk' : n < k := Nat.lt_of_not_ge hk
    have hz : n.choose k = 0 := Nat.choose_eq_zero_of_lt hk'
    have hz' : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hz, hz']

/-- Multiplication by `X` after differentiation acts on a coefficient by its index. -/
private theorem coeff_X_derivative (P : ℤ[X]) (k : ℕ) :
    (X * derivative P).coeff k = (k : ℤ) * P.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
      rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring

/-- The derivative of `X P'` has coefficient `(k+1)^2 P[k+1]`. -/
private theorem coeff_derivative_X_derivative (P : ℤ[X]) (k : ℕ) :
    (derivative (X * derivative P)).coeff k =
      ((k : ℤ) + 1) ^ 2 * P.coeff (k + 1) := by
  rw [coeff_derivative, coeff_X_mul, coeff_derivative]
  ring

/-- The integral Deuring polynomial satisfies its hypergeometric differential equation
in Euler-operator form. -/
theorem deuringPolynomial_euler_equation (n : ℕ) :
    derivative (X * derivative (deuringPolynomial n)) -
      X * derivative (X * derivative (deuringPolynomial n)) +
      C (2 * (n : ℤ)) * (X * derivative (deuringPolynomial n)) -
      C ((n : ℤ) ^ 2) * deuringPolynomial n = 0 := by
  apply Polynomial.ext
  intro k
  simp only [coeff_sub, coeff_add, coeff_zero, coeff_C_mul]
  rw [coeff_derivative_X_derivative, coeff_X_derivative,
    coeff_X_derivative, coeff_deuringPolynomial, coeff_deuringPolynomial]
  nlinarith [choose_square_recurrence n k]

/-- The differential equation in the usual second-order form. -/
theorem deuringPolynomial_differential_equation (n : ℕ) :
    X * (1 - X) * derivative (derivative (deuringPolynomial n)) +
      (1 - X + C (2 * (n : ℤ)) * X) * derivative (deuringPolynomial n) -
      C ((n : ℤ) ^ 2) * deuringPolynomial n = 0 := by
  have h := deuringPolynomial_euler_equation n
  simp only [derivative_mul, derivative_X, one_mul] at h
  convert h using 1; ring

/-- The constant coefficient, equivalently the value at zero, is one. -/
theorem deuringPolynomial_eval_zero (n : ℕ) :
    (deuringPolynomial n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_deuringPolynomial]
  simp

/-- The Deuring polynomial is monic of degree `n`. -/
theorem deuringPolynomial_monic_degree (n : ℕ) :
    (deuringPolynomial n).Monic ∧ (deuringPolynomial n).natDegree = n := by
  have hbound : (deuringPolynomial n).degree ≤ (n : WithBot ℕ) := by
    apply (degree_le_iff_coeff_zero _ _).2
    intro k hk
    rw [coeff_deuringPolynomial]
    have hkn : n < k := by exact_mod_cast hk
    simp [Nat.choose_eq_zero_of_lt hkn]
  have hcoeff : (deuringPolynomial n).coeff n = 1 := by
    simp [coeff_deuringPolynomial]
  have hdegree : (deuringPolynomial n).degree = (n : WithBot ℕ) := by
    apply le_antisymm hbound
    exact le_degree_of_ne_zero (by simp [hcoeff])
  have hnat : (deuringPolynomial n).natDegree = n :=
    natDegree_eq_of_degree_eq_some hdegree
  constructor
  · show (deuringPolynomial n).leadingCoeff = 1
    rw [← coeff_natDegree, hnat, hcoeff]
  · exact hnat

/-- Vandermonde's convolution at the middle coefficient. -/
private theorem sum_choose_squares (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) ^ 2) =
      ((2 * n).choose n : ℤ) := by
  classical
  have hsum :
      (∑ ij ∈ Finset.antidiagonal n,
        (n.choose ij.1 : ℤ) * (n.choose ij.2 : ℤ)) =
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) ^ 2 := by
    refine Finset.sum_bij (fun ij _ => ij.1) ?_ ?_ ?_ ?_
    · intro ij hij
      have h := Finset.mem_antidiagonal.mp hij
      simp only [Finset.mem_range]
      omega
    · intro a ha b hb heq
      have ha' := Finset.mem_antidiagonal.mp ha
      have hb' := Finset.mem_antidiagonal.mp hb
      apply Prod.ext
      · exact heq
      · omega
    · intro i hi
      refine ⟨(i, n - i), ?_, rfl⟩
      apply Finset.mem_antidiagonal.mpr
      have hle : i ≤ n := by
        have hi' : i < n + 1 := Finset.mem_range.mp hi
        omega
      omega
    · intro ij hij
      have h := Finset.mem_antidiagonal.mp hij
      have hle : ij.1 ≤ n := by omega
      have heq : ij.2 = n - ij.1 := by omega
      rw [heq, Nat.choose_symm hle]
      ring
  have hp :
      ((1 + X : ℤ[X]) ^ n * (1 + X : ℤ[X]) ^ n).coeff n =
        ((2 * n).choose n : ℤ) := by
    rw [← pow_add]
    simpa [two_mul] using (coeff_one_add_X_pow ℤ (2 * n) n)
  rw [coeff_mul] at hp
  simp only [coeff_one_add_X_pow] at hp
  exact hsum.symm.trans hp

/-- Evaluation at one is the central binomial coefficient. -/
theorem deuringPolynomial_eval_one (n : ℕ) :
    (deuringPolynomial n).eval 1 = ((2 * n).choose n : ℤ) := by
  change (evalRingHom (1 : ℤ)) (deuringPolynomial n) = _
  simp [deuringPolynomial, sum_choose_squares]


end SptClassification
