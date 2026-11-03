/- Assembled by AxiomProver. -/

module

public import SptClassification.EllipticCurves.DeuringPolynomial
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.Separable

/-!
# Reduction of the Deuring polynomial

These coefficient and differential identities provide the polynomial part of
the Legendre Hasse-invariant calculation in [silverman2009, Chapter V].
The geometric identification with a Hasse section is a separate construction.
-/

public section

namespace SptClassification

open Polynomial

/-- The Deuring polynomial with coefficients in a commutative ring. -/
@[expose] noncomputable def deuringPolynomialIn (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  (deuringPolynomial n).map (Int.castRingHom R)

theorem coeff_deuringPolynomialIn (R : Type*) [CommRing R] (n k : ℕ) :
    (deuringPolynomialIn R n).coeff k = (n.choose k : R) ^ 2 := by
  simp [deuringPolynomialIn, coeff_deuringPolynomial]

theorem deuringPolynomialIn_eval (R : Type*) [CommRing R] (n : ℕ) (x : R) :
    (deuringPolynomialIn R n).eval x =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : R) ^ 2 * x ^ i := by
  classical
  have hsum (s : Finset ℕ) :
      eval₂ (Int.castRingHom R) x
          (∑ i ∈ s, monomial i ((n.choose i : ℤ) ^ 2)) =
        ∑ i ∈ s, (n.choose i : R) ^ 2 * x ^ i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        simp [his, eval₂_add, eval₂_monomial, ih]
  simpa [deuringPolynomialIn, deuringPolynomial, eval_map] using
    hsum (Finset.range (n + 1))

theorem deuringPolynomialIn_eval_zero (R : Type*) [CommRing R] (n : ℕ) :
    (deuringPolynomialIn R n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_deuringPolynomialIn]
  simp

theorem deuringPolynomialIn_eval_one (R : Type*) [CommRing R] (n : ℕ) :
    (deuringPolynomialIn R n).eval 1 = ((2 * n).choose n : R) := by
  simp [deuringPolynomialIn, Polynomial.eval_map, deuringPolynomial_eval_one]

/-- The binomial coefficients in the first half of row `2n` alternate modulo `2n+1`. -/
private theorem choose_two_mul_mod (n k : ℕ) [Fact (Nat.Prime (2 * n + 1))]
    (hk : k ≤ n) :
    ((2 * n).choose k : ZMod (2 * n + 1)) = (-1 : ZMod (2 * n + 1)) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k ≤ n := by omega
      have hr := congrArg (fun a : ℕ => (a : ZMod (2 * n + 1)))
        (Nat.choose_succ_right_eq (2 * n) k)
      simp only [Nat.cast_mul] at hr
      have hp : ((2 * n : ℕ) : ZMod (2 * n + 1)) = -1 := by
        have hzero : ((2 * n : ℕ) : ZMod (2 * n + 1)) + 1 = 0 := by
          simpa only [Nat.cast_add, Nat.cast_one] using
            (ZMod.natCast_self (2 * n + 1))
        exact eq_neg_of_add_eq_zero_left hzero
      have hsub : ((2 * n - k : ℕ) : ZMod (2 * n + 1)) =
          -((k + 1 : ℕ) : ZMod (2 * n + 1)) := by
        rw [Nat.cast_sub (by omega : k ≤ 2 * n), hp]
        push_cast
        ring
      have hnz : ((k + 1 : ℕ) : ZMod (2 * n + 1)) ≠ 0 := by
        intro hz
        have hdiv := (ZMod.natCast_eq_zero_iff (k + 1) (2 * n + 1)).mp hz
        have hle := Nat.le_of_dvd (by omega : 0 < k + 1) hdiv
        omega
      apply (mul_right_cancel₀ hnz)
      calc
        ((2 * n).choose (k + 1) : ZMod (2 * n + 1)) *
            ((k + 1 : ℕ) : ZMod (2 * n + 1)) =
            ((2 * n).choose k : ZMod (2 * n + 1)) *
              ((2 * n - k : ℕ) : ZMod (2 * n + 1)) := hr
        _ = (-1 : ZMod (2 * n + 1)) ^ (k + 1) *
            ((k + 1 : ℕ) : ZMod (2 * n + 1)) := by
          rw [ih hk', hsub, pow_succ]
          ring

theorem deuringPolynomialIn_eval_one_mod (n : ℕ)
    [Fact (Nat.Prime (2 * n + 1))] :
    (deuringPolynomialIn (ZMod (2 * n + 1)) n).eval 1 =
      (-1 : ZMod (2 * n + 1)) ^ n := by
  rw [deuringPolynomialIn_eval_one]
  exact choose_two_mul_mod n n le_rfl

/-- Base change preserves the Deuring differential equation. -/
theorem deuringPolynomialIn_differential_equation (R : Type*) [CommRing R] (n : ℕ) :
    X * (1 - X) * derivative (derivative (deuringPolynomialIn R n)) +
      (1 - X + C (2 * (n : R)) * X) * derivative (deuringPolynomialIn R n) -
      C ((n : R) ^ 2) * deuringPolynomialIn R n = 0 := by
  have h := congrArg (Polynomial.map (Int.castRingHom R))
    (deuringPolynomial_differential_equation n)
  simp [deuringPolynomialIn, Polynomial.derivative_map] at h ⊢
  have hC : (C (2 : R) : R[X]) = 2 := by
    calc
      C (2 : R) = C (1 + 1 : R) := by ring
      _ = (1 : R[X]) + 1 := by simp
      _ = 2 := by ring
  rw [hC]
  exact h

/-- The middle coefficient in the product of two binomial polynomials. -/
private theorem coeff_binomial_product (R : Type*) [CommRing R]
    (r s : R) (n : ℕ) :
    (((X + C r) ^ n * (X + C s) ^ n : R[X]).coeff n) =
      ∑ i ∈ Finset.range (n + 1),
        r ^ i * s ^ (n - i) * (n.choose i : R) ^ 2 := by
  classical
  rw [coeff_mul]
  simp only [coeff_X_add_C_pow]
  refine Finset.sum_bij (fun ij _ => ij.2) ?_ ?_ ?_ ?_
  · intro ij hij
    have h := Finset.mem_antidiagonal.mp hij
    simp only [Finset.mem_range]
    omega
  · intro a ha b hb heq
    have ha' := Finset.mem_antidiagonal.mp ha
    have hb' := Finset.mem_antidiagonal.mp hb
    apply Prod.ext
    · omega
    · exact heq
  · intro i hi
    refine ⟨(n - i, i), ?_, rfl⟩
    apply Finset.mem_antidiagonal.mpr
    have hle : i ≤ n := by
      have hi' : i < n + 1 := Finset.mem_range.mp hi
      omega
    omega
  · intro ij hij
    have h := Finset.mem_antidiagonal.mp hij
    have hle : ij.2 ≤ n := by omega
    have heq : ij.1 = n - ij.2 := by omega
    rw [heq, Nat.choose_symm hle]
    have hsub : n - (n - ij.2) = ij.2 := by omega
    rw [hsub]
    ring

/-- The Legendre cubic coefficient is the Deuring polynomial, up to the standard sign. -/
theorem coeff_legendreCubic_pow (R : Type*) [CommRing R] (n : ℕ) (lam : R) :
    ((X * (X - 1) * (X - C lam)) ^ n : R[X]).coeff (2 * n) =
      (-1 : R) ^ n * (deuringPolynomialIn R n).eval lam := by
  have heq : (X * (X - 1) * (X - C lam) : R[X]) ^ n =
      X ^ n * ((X + C (-lam)) ^ n * (X + C (-1 : R)) ^ n) := by
    simp only [mul_pow]
    simp only [map_neg, map_one]
    ring
  rw [heq, show 2 * n = n + n by omega, coeff_X_pow_mul]
  rw [coeff_binomial_product, deuringPolynomialIn_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ n := by
    have hi' : i < n + 1 := Finset.mem_range.mp hi
    omega
  calc
    (-lam) ^ i * (-1 : R) ^ (n - i) * (n.choose i : R) ^ 2 =
        ((-1 : R) ^ i * (-1 : R) ^ (n - i)) *
          ((n.choose i : R) ^ 2 * lam ^ i) := by
            rw [show -lam = (-1 : R) * lam by ring, mul_pow]
            ring
    _ = (-1 : R) ^ n * ((n.choose i : R) ^ 2 * lam ^ i) := by
      rw [← pow_add, show i + (n - i) = n by omega]

theorem deuringPolynomialIn_monic_degree (R : Type*) [CommRing R] [Nontrivial R] (n : ℕ) :
    (deuringPolynomialIn R n).Monic ∧ (deuringPolynomialIn R n).natDegree = n := by
  have hbound : (deuringPolynomialIn R n).degree ≤ (n : WithBot ℕ) := by
    apply (degree_le_iff_coeff_zero _ _).2
    intro k hk
    rw [coeff_deuringPolynomialIn]
    have hkn : n < k := by exact_mod_cast hk
    simp [Nat.choose_eq_zero_of_lt hkn]
  have hcoeff : (deuringPolynomialIn R n).coeff n = 1 := by
    simp [coeff_deuringPolynomialIn]
  have hdegree : (deuringPolynomialIn R n).degree = (n : WithBot ℕ) := by
    apply le_antisymm hbound
    exact le_degree_of_ne_zero (by simp [hcoeff])
  have hnat : (deuringPolynomialIn R n).natDegree = n :=
    natDegree_eq_of_degree_eq_some hdegree
  constructor
  · show (deuringPolynomialIn R n).leadingCoeff = 1
    rw [← coeff_natDegree, hnat, hcoeff]
  · exact hnat

end SptClassification
