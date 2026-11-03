/- Assembled by AxiomProver. -/

module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.CharP.Frobenius

/-!
# Cartier operator on polynomial differentials

We first isolate the coefficient extraction in the Cartier formula. Over a
perfect field in characteristic `p`, inverse Frobenius on coefficients will
turn it into the operator on polynomial differentials. See
[silverman2009, Chapter V].
-/

public section

namespace SptClassification

open Polynomial

/-- The terms of a polynomial differential whose degree is congruent to
`p - 1` modulo `p`, with exponents divided by `p`. -/
@[expose] noncomputable def cartierExtract {R : Type*} [CommRing R]
    (p : ℕ) (A : R[X]) : R[X] :=
  ∑ j ∈ Finset.range (A.natDegree + 1),
    monomial j (A.coeff (p * j + (p - 1)))

/-- Coefficients of the extracted polynomial differential. -/
theorem coeff_cartierExtract {R : Type*} [CommRing R]
    (p : ℕ) (hp : 0 < p) (A : R[X]) (j : ℕ) :
    (cartierExtract p A).coeff j = A.coeff (p * j + (p - 1)) := by
  classical
  by_cases hj : j ≤ A.natDegree
  · simp [cartierExtract, coeff_monomial, Finset.sum_ite_eq', hj]
  · have hmul : j ≤ p * j := by
      simpa using Nat.mul_le_mul_right j hp
    have hindex : A.natDegree < p * j + (p - 1) := by omega
    have hz := coeff_eq_zero_of_natDegree_lt hindex
    simp [cartierExtract, coeff_monomial, Finset.sum_ite_eq', hj, hz]

/-- Coefficient extraction is additive. -/
theorem cartierExtract_add {R : Type*} [CommRing R]
    (p : ℕ) (hp : 0 < p) (A B : R[X]) :
    cartierExtract p (A + B) = cartierExtract p A + cartierExtract p B := by
  apply Polynomial.ext
  intro j
  simp [coeff_cartierExtract _ hp]

/-- In characteristic `p`, extraction kills an exact polynomial differential. -/
theorem cartierExtract_derivative {R : Type*} [CommRing R]
    (p : ℕ) (hp : 0 < p) (hchar : (p : R) = 0) (A : R[X]) :
    cartierExtract p (derivative A) = 0 := by
  apply Polynomial.ext
  intro j
  rw [coeff_cartierExtract _ hp, coeff_derivative, coeff_zero]
  have hindex : p * j + (p - 1) + 1 = p * (j + 1) := by
    rw [Nat.mul_add, mul_one]
    omega
  have hscalar : ((p * j + (p - 1) : ℕ) : R) + 1 = 0 := by
    calc
      ((p * j + (p - 1) : ℕ) : R) + 1 =
          ((p * j + (p - 1) + 1 : ℕ) : R) := by push_cast; ring
      _ = (p : R) * ((j + 1 : ℕ) : R) := by rw [hindex]; push_cast; ring
      _ = 0 := by simp [hchar]
  have hcast : (p : R) * (j : R) + ((p - 1 : ℕ) : R) + 1 = 0 := by
    calc
      (p : R) * (j : R) + ((p - 1 : ℕ) : R) + 1 =
          ((p * j + (p - 1) : ℕ) : R) + 1 := by push_cast; ring
      _ = 0 := hscalar
  simp [hcast]

/-- Cartier on polynomial differentials, using inverse Frobenius on the
extracted coefficients. The equivalence is Frobenius for a perfect field. -/
@[expose] noncomputable def polynomialCartier {k : Type*} [Field k]
    (p : ℕ) (frobeniusEquiv : k ≃+* k) (A : k[X]) : k[X] :=
  (cartierExtract p A).map frobeniusEquiv.symm.toRingHom

/-- The coefficient formula for polynomial Cartier. -/
theorem coeff_polynomialCartier {k : Type*} [Field k]
    (p : ℕ) (hp : 0 < p) (frobeniusEquiv : k ≃+* k) (A : k[X]) (j : ℕ) :
    (polynomialCartier p frobeniusEquiv A).coeff j =
      frobeniusEquiv.symm (A.coeff (p * j + (p - 1))) := by
  simp [polynomialCartier, coeff_cartierExtract p hp]

/-- A polynomial differential of degree below `2p-1` has constant Cartier
image, determined by its coefficient in degree `p-1`. -/
theorem polynomialCartier_eq_C_of_natDegree_lt {k : Type*} [Field k]
    (p : ℕ) (hp : 0 < p) (frobeniusEquiv : k ≃+* k) (A : k[X])
    (hdegree : A.natDegree < 2 * p - 1) :
    polynomialCartier p frobeniusEquiv A =
      C (frobeniusEquiv.symm (A.coeff (p - 1))) := by
  apply Polynomial.ext
  intro j
  cases j with
  | zero => simp [coeff_polynomialCartier p hp]
  | succ j =>
      have hmul : p * 1 ≤ p * (j + 1) :=
        Nat.mul_le_mul_left p (by omega)
      have hindex : A.natDegree < p * (j + 1) + (p - 1) := by omega
      rw [coeff_polynomialCartier p hp]
      rw [coeff_eq_zero_of_natDegree_lt hindex]
      simp

/-- Polynomial Cartier is additive. -/
theorem polynomialCartier_add {k : Type*} [Field k]
    (p : ℕ) (hp : 0 < p) (frobeniusEquiv : k ≃+* k) (A B : k[X]) :
    polynomialCartier p frobeniusEquiv (A + B) =
      polynomialCartier p frobeniusEquiv A + polynomialCartier p frobeniusEquiv B := by
  simp [polynomialCartier, cartierExtract_add p hp]

/-- Polynomial Cartier annihilates exact differentials. -/
theorem polynomialCartier_derivative {k : Type*} [Field k]
    (p : ℕ) (hp : 0 < p) (hchar : (p : k) = 0)
    (frobeniusEquiv : k ≃+* k) (A : k[X]) :
    polynomialCartier p frobeniusEquiv (derivative A) = 0 := by
  simp [polynomialCartier, cartierExtract_derivative p hp hchar]

/-- The Frobenius equivalence of a field with bijective Frobenius. -/
@[expose] noncomputable def perfectFrobeniusEquiv {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p)) :
    k ≃+* k :=
  RingEquiv.ofBijective (frobenius k p) hperfect

theorem perfectFrobeniusEquiv_apply {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (a : k) : perfectFrobeniusEquiv p hperfect a = a ^ p := by
  rfl

/-- Raw extraction commutes with multiplication by a constant. -/
theorem cartierExtract_C_mul {R : Type*} [CommRing R]
    (p : ℕ) (hp : 0 < p) (a : R) (A : R[X]) :
    cartierExtract p (C a * A) = C a * cartierExtract p A := by
  apply Polynomial.ext
  intro j
  simp [coeff_cartierExtract p hp]

/-- Raw extraction divides a multiple-of-`p` monomial shift by `p`. -/
theorem cartierExtract_X_pow_mul {R : Type*} [CommRing R]
    (p : ℕ) (hp : 0 < p) (n : ℕ) (A : R[X]) :
    cartierExtract p (X ^ (p * n) * A) = X ^ n * cartierExtract p A := by
  apply Polynomial.ext
  intro j
  rw [coeff_cartierExtract p hp, coeff_X_pow_mul', coeff_X_pow_mul']
  by_cases hj : n ≤ j
  · have hindex : p * n ≤ p * j + (p - 1) := by
      have hmul := Nat.mul_le_mul_left p hj
      omega
    simp only [hj, hindex, ite_true, ite_false, coeff_cartierExtract p hp]
    have heq : p * j + (p - 1) - p * n = p * (j - n) + (p - 1) := by
      have hj' : j = n + (j - n) := by omega
      conv_lhs => rw [hj']
      rw [Nat.mul_add]
      omega
    rw [heq]
  · have hindex : ¬ p * n ≤ p * j + (p - 1) := by
      have hj' : j + 1 ≤ n := by omega
      have hmul := Nat.mul_le_mul_left p hj'
      rw [Nat.mul_add, mul_one] at hmul
      omega
    simp only [hj, hindex, ite_true, ite_false]

/-- Inverse Frobenius converts scalar multiplication into twisted scalar
multiplication under Cartier. -/
theorem polynomialCartier_C_mul {k : Type*} [Field k]
    (p : ℕ) (hp : 0 < p) (frobeniusEquiv : k ≃+* k)
    (a : k) (A : k[X]) :
    polynomialCartier p frobeniusEquiv (C a * A) =
      C (frobeniusEquiv.symm a) * polynomialCartier p frobeniusEquiv A := by
  simp [polynomialCartier, cartierExtract_C_mul p hp, Polynomial.map_mul]

/-- Cartier divides a multiple-of-`p` shift of the exponent by `p`. -/
theorem polynomialCartier_X_pow_mul {k : Type*} [Field k]
    (p : ℕ) (hp : 0 < p) (frobeniusEquiv : k ≃+* k)
    (n : ℕ) (A : k[X]) :
    polynomialCartier p frobeniusEquiv (X ^ (p * n) * A) =
      X ^ n * polynomialCartier p frobeniusEquiv A := by
  simp [polynomialCartier, cartierExtract_X_pow_mul p hp, Polynomial.map_mul]

/-- Cartier is linear over a Frobenius `p`-th power of a monomial. -/
theorem polynomialCartier_monomial_pow_mul {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (n : ℕ) (a : k) (A : k[X]) :
    polynomialCartier p (perfectFrobeniusEquiv p hperfect)
        ((monomial n a) ^ p * A) =
      monomial n a * polynomialCartier p (perfectFrobeniusEquiv p hperfect) A := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hroot : (perfectFrobeniusEquiv p hperfect).symm (a ^ p) = a := by
    rw [← perfectFrobeniusEquiv_apply p hperfect a]
    exact RingEquiv.symm_apply_apply _ _
  have hmonomial : monomial n a = C a * X ^ n := by
    ext j
    simp [coeff_monomial, coeff_C_mul, coeff_X_pow, eq_comm]
  rw [hmonomial, mul_pow, ← C_pow, ← pow_mul, mul_comm n p,
    mul_assoc, polynomialCartier_C_mul p hp,
    polynomialCartier_X_pow_mul p hp, hroot]
  ring

/-- Cartier is Frobenius semilinear on polynomial differentials. -/
theorem polynomialCartier_pow_mul {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (g A : k[X]) :
    polynomialCartier p (perfectFrobeniusEquiv p hperfect) (g ^ p * A) =
      g * polynomialCartier p (perfectFrobeniusEquiv p hperfect) A := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  induction g using Polynomial.induction_on' with
  | add g h hg hh =>
      have hpow : (g + h) ^ p = g ^ p + h ^ p := by
        have hfrob := (frobenius k[X] p).map_add g h
        exact hfrob
      rw [hpow, add_mul, polynomialCartier_add p hp, hg, hh, add_mul]
  | monomial n a =>
      exact polynomialCartier_monomial_pow_mul p hperfect n a A

end SptClassification
