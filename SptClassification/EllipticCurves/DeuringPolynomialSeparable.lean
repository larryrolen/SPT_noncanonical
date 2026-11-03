/- Assembled by AxiomProver. -/

module

public import SptClassification.EllipticCurves.DeuringPolynomialReduction
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Simple roots of the Deuring polynomial

The differential equation rules out a repeated root away from its singular points.
We first isolate the coefficient argument at the origin, then translate an arbitrary
root to the origin.

This is elementary polynomial support for the Hasse-invariant argument of
[rolenManuscript, Section 4]; see [silverman2009, Chapter V] for the
elliptic-curve context. No modular-curve identification is asserted here.
-/

public section

namespace SptClassification

open Polynomial

private theorem coeff_mul_zero_of_lower_coeffs {R : Type*} [CommRing R]
    (A P : R[X]) (k : ℕ) (h : ∀ i ≤ k, P.coeff i = 0) :
    (A * P).coeff k = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hle : ij.2 ≤ k := by
    have hs := Finset.mem_antidiagonal.mp hij
    omega
  simp [h _ hle]

private theorem coeff_mul_derivative_zero_of_lower_coeffs {R : Type*} [CommRing R]
    (A P : R[X]) (k : ℕ) (h : ∀ i ≤ k + 1, P.coeff i = 0) :
    (A * derivative P).coeff k = 0 := by
  apply coeff_mul_zero_of_lower_coeffs
  intro i hi
  rw [coeff_derivative, h _ (by omega)]
  simp

private theorem coeff_mul_second_derivative_of_lower_coeffs {R : Type*} [CommRing R]
    (A P : R[X]) (k : ℕ) (h : ∀ i ≤ k + 1, P.coeff i = 0) :
    (A * derivative (derivative P)).coeff k =
      A.coeff 0 * ((k + 2 : ℕ) : R) * ((k + 1 : ℕ) : R) * P.coeff (k + 2) := by
  classical
  rw [coeff_mul]
  have hsingle :
      (∑ ij ∈ Finset.antidiagonal k,
          A.coeff ij.1 * (derivative (derivative P)).coeff ij.2) =
        A.coeff 0 * (derivative (derivative P)).coeff k := by
    apply Finset.sum_eq_single (0, k)
    · intro ij hij hne
      have hs := Finset.mem_antidiagonal.mp hij
      have hpos : 0 < ij.1 := by
        by_contra hn
        have hz : ij.1 = 0 := by omega
        have hk : ij.2 = k := by omega
        exact hne (Prod.ext hz hk)
      have hlt : ij.2 < k := by omega
      rw [coeff_derivative, coeff_derivative, h _ (by omega)]
      ring
    · simp
  rw [hsingle, coeff_derivative, coeff_derivative]
  push_cast
  ring

/-- An ODE with a nonzero leading coefficient has no nonzero solution with a
double zero at the origin while all relevant integers remain nonzero. -/
private theorem eq_zero_of_ode_double_zero {K : Type*} [Field K]
    (A B C P : K[X]) (n : ℕ)
    (hode : A * derivative (derivative P) + B * derivative P + C * P = 0)
    (hA : A.coeff 0 ≠ 0)
    (h0 : P.coeff 0 = 0)
    (h1 : (derivative P).coeff 0 = 0)
    (hsmall : ∀ k, 0 < k → k ≤ n → (k : K) ≠ 0)
    (hdeg : P.natDegree ≤ n) : P = 0 := by
  have hcoeff : ∀ k ≤ n, P.coeff k = 0 := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hz : k = 0
      · simpa [hz] using h0
      by_cases ho : k = 1
      · subst k
        simpa [coeff_derivative] using h1
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have hprev : ∀ i ≤ j + 1, P.coeff i = 0 := by
        intro i hi
        exact ih i (by omega) (by omega)
      have hodecoeff := congrArg (fun Q : K[X] => Q.coeff j) hode
      simp only [coeff_add, coeff_zero] at hodecoeff
      rw [coeff_mul_second_derivative_of_lower_coeffs A P j hprev,
        coeff_mul_derivative_zero_of_lower_coeffs B P j hprev,
        coeff_mul_zero_of_lower_coeffs C P j (fun i hi => hprev i (by omega))] at hodecoeff
      simp only [add_zero] at hodecoeff
      have hfactor : A.coeff 0 * ((j + 2 : ℕ) : K) * ((j + 1 : ℕ) : K) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hA (hsmall _ (by omega) (by omega)))
          (hsmall _ (by omega) (by omega))
      exact (mul_eq_zero.mp hodecoeff).resolve_left hfactor
  apply Polynomial.ext
  intro k
  rw [coeff_zero]
  by_cases hk : k ≤ n
  · exact hcoeff k hk
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- At an ordinary point of the differential equation, a nonzero solution has no
common zero with its derivative. -/
private theorem no_common_root_of_ode {K : Type*} [Field K]
    (A B E P : K[X]) (n : ℕ)
    (hode : A * derivative (derivative P) + B * derivative P + E * P = 0)
    (hA : ∀ a : K, P.eval a = 0 → A.eval a ≠ 0)
    (hP : P ≠ 0)
    (hsmall : ∀ k, 0 < k → k ≤ n → (k : K) ≠ 0)
    (hdeg : P.natDegree ≤ n) (a : K) :
    P.eval a ≠ 0 ∨ (derivative P).eval a ≠ 0 := by
  by_contra h
  push Not at h
  rcases h with ⟨hp, hp'⟩
  let T : K[X] := X + C a
  have hderiv (Q : K[X]) : derivative (Q.comp T) = (derivative Q).comp T := by
    simp [derivative_comp, T]
  have hode' :
      A.comp T * derivative (derivative (P.comp T)) +
        B.comp T * derivative (P.comp T) + E.comp T * P.comp T = 0 := by
    have hh := congrArg (fun Q : K[X] => Q.comp T) hode
    simpa only [add_comp, mul_comp, zero_comp, hderiv] using hh
  have hA' : (A.comp T).coeff 0 ≠ 0 := by
    simpa [coeff_zero_eq_eval_zero, eval_comp, T] using hA a hp
  have h0 : (P.comp T).coeff 0 = 0 := by
    simpa [coeff_zero_eq_eval_zero, eval_comp, T] using hp
  have h1 : (derivative (P.comp T)).coeff 0 = 0 := by
    simpa [hderiv, coeff_zero_eq_eval_zero, eval_comp, T] using hp'
  have hdeg' : (P.comp T).natDegree ≤ n := by
    calc
      (P.comp T).natDegree ≤ P.natDegree * T.natDegree := natDegree_comp_le
      _ = P.natDegree := by simp [T]
      _ ≤ n := hdeg
  have hz := eq_zero_of_ode_double_zero (A.comp T) (B.comp T) (E.comp T)
    (P.comp T) n hode' hA' h0 h1 hsmall hdeg'
  exact hP (comp_X_add_C_eq_zero_iff.mp hz)

/-- The Deuring polynomial has simple roots over an algebraic closure of its
coefficient field in characteristic `2n+1`. -/
private theorem deuringPolynomialIn_separable_closure (n : ℕ)
    [Fact (Nat.Prime (2 * n + 1))] :
    (deuringPolynomialIn (AlgebraicClosure (ZMod (2 * n + 1))) n).Separable := by
  let K := AlgebraicClosure (ZMod (2 * n + 1))
  let P : K[X] := deuringPolynomialIn K n
  let A : K[X] := X * (1 - X)
  let B : K[X] := 1 - X + C (2 * (n : K)) * X
  let E : K[X] := -C ((n : K) ^ 2)
  have hdegree : P.natDegree = n := (deuringPolynomialIn_monic_degree K n).2
  have hP : P ≠ 0 := (deuringPolynomialIn_monic_degree K n).1.ne_zero
  have hzero : P.eval 0 = 1 := deuringPolynomialIn_eval_zero K n
  have hone : P.eval 1 = (-1 : K) ^ n := by
    have hmod := deuringPolynomialIn_eval_one_mod n
    rw [deuringPolynomialIn_eval_one] at hmod
    have hmapped := congrArg (algebraMap (ZMod (2 * n + 1)) K) hmod
    simpa [P, deuringPolynomialIn_eval_one] using hmapped
  have hA : ∀ a : K, P.eval a = 0 → A.eval a ≠ 0 := by
    intro a ha
    have ha0 : a ≠ 0 := by
      intro h
      subst a
      simp [hzero] at ha
    have ha1 : a ≠ 1 := by
      intro h
      subst a
      simp [hone] at ha
    simpa [A] using mul_ne_zero ha0 (sub_ne_zero.mpr ha1.symm)
  have hsmall : ∀ k, 0 < k → k ≤ n → (k : K) ≠ 0 := by
    intro k hk hkn hz
    have hd : 2 * n + 1 ∣ k := (CharP.cast_eq_zero_iff K (2 * n + 1) k).mp hz
    have hle : 2 * n + 1 ≤ k := Nat.le_of_dvd hk hd
    omega
  have hode : A * derivative (derivative P) + B * derivative P + E * P = 0 := by
    simpa [A, B, E, P, sub_eq_add_neg, neg_mul] using
      deuringPolynomialIn_differential_equation K n
  apply (separable_def P).2
  apply (isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K P (derivative P)).2
  intro a
  simpa [Polynomial.coe_aeval_eq_eval] using
    no_common_root_of_ode A B E P n hode hA hP hsmall hdegree.le a

/-- The coefficientwise reduction of the Deuring polynomial modulo `2n+1`
is separable. -/
theorem deuringPolynomialIn_separable (n : ℕ)
    [Fact (Nat.Prime (2 * n + 1))] :
    (deuringPolynomialIn (ZMod (2 * n + 1)) n).Separable := by
  let F := ZMod (2 * n + 1)
  let K := AlgebraicClosure F
  have hmap :
      (deuringPolynomialIn F n).map (algebraMap F K) =
        deuringPolynomialIn K n := by
    apply Polynomial.ext
    intro k
    simp only [coeff_map, coeff_deuringPolynomialIn, map_pow, algebraMap.coe_natCast]
  apply (separable_map (algebraMap F K)).mp
  rw [hmap]
  exact deuringPolynomialIn_separable_closure n

/-- In characteristic `2n+1`, the hypergeometric equation has the usual
Legendre form with parameter `1/4`. -/
theorem deuringPolynomialIn_differential_equation_mod (n : ℕ)
    [Fact (Nat.Prime (2 * n + 1))] :
    let P := deuringPolynomialIn (ZMod (2 * n + 1)) n
    X * (1 - X) * derivative (derivative P) +
      (1 - 2 * X) * derivative P -
      C ((1 : ZMod (2 * n + 1)) / 4) * P = 0 := by
  let F := ZMod (2 * n + 1)
  have hn : 0 < n := by
    have hp := (Fact.out : Nat.Prime (2 * n + 1)).two_le
    omega
  have htwo : (2 : F) * (n : F) = -1 := by
    have hzero : ((2 * n + 1 : ℕ) : F) = 0 := ZMod.natCast_self (2 * n + 1)
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hzero
    rw [Nat.cast_mul] at hzero
    linear_combination hzero
  have h2ne : (2 : F) ≠ 0 := by
    intro hz
    have hd : 2 * n + 1 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * n + 1)).mp hz
    have hle : 2 * n + 1 ≤ 2 := Nat.le_of_dvd (by omega) hd
    omega
  have h4ne : (4 : F) ≠ 0 := by
    have hh : (4 : F) = (2 : F) ^ 2 := by norm_num
    rw [hh]
    exact pow_ne_zero _ h2ne
  have hquarter : (n : F) ^ 2 = (1 : F) / 4 := by
    apply (eq_div_iff h4ne).2
    calc
      (n : F) ^ 2 * 4 = (2 * (n : F)) ^ 2 := by ring
      _ = (-1 : F) ^ 2 := congrArg (· ^ 2) htwo
      _ = 1 := by ring
  have hlinear : (1 - X + C (2 * (n : F)) * X : F[X]) = 1 - 2 * X := by
    have hc : (2 * (n : F)) = -1 := htwo
    rw [hc]
    simp
    ring
  change X * (1 - X) * derivative (derivative (deuringPolynomialIn F n)) +
      (1 - 2 * X) * derivative (deuringPolynomialIn F n) -
      C ((1 : F) / 4) * deuringPolynomialIn F n = 0
  rw [← hlinear, ← hquarter]
  exact deuringPolynomialIn_differential_equation F n

/-- Reduction of the integral Deuring polynomial at a prime at least five has
the expected degree, endpoints, and simple roots. -/
theorem deuringPolynomial_mod_prime_spec (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    let n := (p - 1) / 2
    let P := deuringPolynomialIn (ZMod p) n
    P.Monic ∧ P.natDegree = n ∧ P.eval 0 = 1 ∧
      P.eval 1 = (-1 : ZMod p) ^ n ∧ P.Separable := by
  obtain ⟨n, hn⟩ : Odd p :=
    (Fact.out : p.Prime).odd_of_ne_two (by omega)
  subst p
  have hhalf : (2 * n + 1 - 1) / 2 = n := by omega
  simp only [hhalf]
  constructor
  · exact (deuringPolynomialIn_monic_degree (ZMod (2 * n + 1)) n).1
  constructor
  · exact (deuringPolynomialIn_monic_degree (ZMod (2 * n + 1)) n).2
  constructor
  · exact deuringPolynomialIn_eval_zero (ZMod (2 * n + 1)) n
  constructor
  · exact deuringPolynomialIn_eval_one_mod n
  · exact deuringPolynomialIn_separable n

/-- For an algebra over `𝔽ₚ`, the coefficient in the Legendre cubic power is
the evaluation of the reduced Deuring polynomial, with the standard sign. -/
theorem coeff_legendreCubic_pow_mod_prime (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (R : Type*) [CommRing R] [Algebra (ZMod p) R] (lam : R) :
    let n := (p - 1) / 2
    ((X * (X - 1) * (X - C lam)) ^ n : R[X]).coeff (p - 1) =
      (-1 : R) ^ n *
        ((deuringPolynomialIn (ZMod p) n).map (algebraMap (ZMod p) R)).eval lam := by
  obtain ⟨n, hn⟩ : Odd p :=
    (Fact.out : p.Prime).odd_of_ne_two (by omega)
  subst p
  have hhalf : (2 * n + 1 - 1) / 2 = n := by omega
  have hprev : 2 * n + 1 - 1 = 2 * n := by omega
  have hmap :
      (deuringPolynomialIn (ZMod (2 * n + 1)) n).map
          (algebraMap (ZMod (2 * n + 1)) R) =
        deuringPolynomialIn R n := by
    apply Polynomial.ext
    intro k
    simp only [coeff_map, coeff_deuringPolynomialIn, map_pow, algebraMap.coe_natCast]
  simp only [hhalf]
  rw [hprev]
  rw [hmap]
  exact coeff_legendreCubic_pow R n lam

end SptClassification
