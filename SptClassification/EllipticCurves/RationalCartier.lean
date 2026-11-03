/- Assembled by AxiomProver. -/

module

public import SptClassification.EllipticCurves.PolynomialCartier
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Cartier operator on rational differentials

For a rational differential represented by `(A / B) dX`, the Cartier
formula is `C(A B^(p-1) dX) / B`. The cross-multiplication theorem below
proves that this is independent of the presentation. See
[silverman2009, Chapter V].
-/

public section

namespace SptClassification

open Polynomial

/-- Cross multiplication makes the polynomial Cartier numerator independent
of the rational presentation. -/
theorem polynomialCartier_fraction_cross {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (A B A' B' : k[X]) (h : A * B' = A' * B) :
    polynomialCartier p (perfectFrobeniusEquiv p hperfect)
        (A * B ^ (p - 1)) * B' =
      polynomialCartier p (perfectFrobeniusEquiv p hperfect)
        (A' * B' ^ (p - 1)) * B := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hp' : p = p - 1 + 1 := by omega
  have hinput : B' ^ p * (A * B ^ (p - 1)) =
      B ^ p * (A' * B' ^ (p - 1)) := by
    rw [hp', pow_succ, pow_succ]
    calc
      B' ^ (p - 1) * B' * (A * B ^ (p - 1)) =
          (A * B') * (B * B') ^ (p - 1) := by rw [mul_pow]; ring
      _ = (A' * B) * (B * B') ^ (p - 1) := by rw [h]
      _ = B ^ (p - 1) * B * (A' * B' ^ (p - 1)) := by rw [mul_pow]; ring
  have hcart := congrArg
    (polynomialCartier p (perfectFrobeniusEquiv p hperfect)) hinput
  rw [polynomialCartier_pow_mul p hperfect B' (A * B ^ (p - 1)),
    polynomialCartier_pow_mul p hperfect B (A' * B' ^ (p - 1))] at hcart
  simpa only [mul_comm] using hcart

/-- The common-denominator numerator for a sum transforms by the two
Frobenius factors prescribed by Cartier semilinearity. -/
theorem polynomialCartier_fraction_add {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (A B C D : k[X]) :
    polynomialCartier p (perfectFrobeniusEquiv p hperfect)
        ((A * D + C * B) * (B * D) ^ (p - 1)) =
      D * polynomialCartier p (perfectFrobeniusEquiv p hperfect)
          (A * B ^ (p - 1)) +
      B * polynomialCartier p (perfectFrobeniusEquiv p hperfect)
          (C * D ^ (p - 1)) := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hpred : p = p - 1 + 1 := by omega
  have hBpow : B ^ p = B ^ (p - 1) * B := by
    calc
      B ^ p = B ^ (p - 1 + 1) := congrArg (B ^ ·) hpred
      _ = B ^ (p - 1) * B := pow_succ B _
  have hDpow : D ^ p = D ^ (p - 1) * D := by
    calc
      D ^ p = D ^ (p - 1 + 1) := congrArg (D ^ ·) hpred
      _ = D ^ (p - 1) * D := pow_succ D _
  have hnum :
      (A * D + C * B) * (B * D) ^ (p - 1) =
        D ^ p * (A * B ^ (p - 1)) +
        B ^ p * (C * D ^ (p - 1)) := by
    rw [mul_pow, hBpow, hDpow]
    ring
  rw [hnum, polynomialCartier_add p hp,
    polynomialCartier_pow_mul p hperfect D,
    polynomialCartier_pow_mul p hperfect B]

/-- Cartier on the coefficient of a rational differential `r dX`. -/
@[expose] noncomputable def rationalCartier {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (r : RatFunc k) : RatFunc k :=
  r.liftOn
    (fun A B => RatFunc.mk
      (polynomialCartier p (perfectFrobeniusEquiv p hperfect)
        (A * B ^ (p - 1))) B)
    (by
      intro A B A' B' hB hB' h
      have hB0 : B ≠ 0 := nonZeroDivisors.ne_zero hB
      have hB'0 : B' ≠ 0 := nonZeroDivisors.ne_zero hB'
      apply (RatFunc.mk_eq_mk hB0 hB'0).2
      apply polynomialCartier_fraction_cross p hperfect
      simpa only [mul_comm] using h)

/-- The formula for Cartier on an actual rational presentation. -/
theorem rationalCartier_mk {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (A B : k[X]) (hB : B ≠ 0) :
    rationalCartier p hperfect (RatFunc.mk A B) =
      RatFunc.mk
        (polynomialCartier p (perfectFrobeniusEquiv p hperfect)
          (A * B ^ (p - 1))) B := by
  unfold rationalCartier
  rw [RatFunc.mk_eq_localization_mk A hB]
  simp only [RatFunc.liftOn_ofFractionRing_mk]

/-- Rational Cartier agrees with polynomial Cartier on a denominator-one
presentation. -/
theorem rationalCartier_mk_one {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p)) (A : k[X]) :
    rationalCartier p hperfect (RatFunc.mk A 1) =
      RatFunc.mk
        (polynomialCartier p (perfectFrobeniusEquiv p hperfect) A) 1 := by
  simpa using rationalCartier_mk p hperfect A 1 one_ne_zero

/-- Addition of rational presentations with nonzero denominators. -/
theorem ratFunc_mk_add {k : Type*} [Field k]
    (A B C D : k[X]) (hB : B ≠ 0) (hD : D ≠ 0) :
    RatFunc.mk A B + RatFunc.mk C D =
      RatFunc.mk (A * D + C * B) (B * D) := by
  have hBmap : algebraMap k[X] (RatFunc k) B ≠ 0 := RatFunc.algebraMap_ne_zero hB
  have hDmap : algebraMap k[X] (RatFunc k) D ≠ 0 := RatFunc.algebraMap_ne_zero hD
  simp only [RatFunc.mk_eq_div, map_add, map_mul]
  field_simp

/-- Cartier on rational differentials is additive. -/
theorem rationalCartier_add {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (r s : RatFunc k) :
    rationalCartier p hperfect (r + s) =
      rationalCartier p hperfect r + rationalCartier p hperfect s := by
  induction r using RatFunc.induction_on' with
  | _ A B hB =>
    induction s using RatFunc.induction_on' with
    | _ C D hD =>
      rw [ratFunc_mk_add A B C D hB hD,
        rationalCartier_mk p hperfect _ _ (mul_ne_zero hB hD),
        rationalCartier_mk p hperfect _ _ hB,
        rationalCartier_mk p hperfect _ _ hD,
        polynomialCartier_fraction_add p hperfect A B C D]
      have hsum := ratFunc_mk_add
        (polynomialCartier p (perfectFrobeniusEquiv p hperfect) (A * B ^ (p - 1))) B
        (polynomialCartier p (perfectFrobeniusEquiv p hperfect) (C * D ^ (p - 1))) D
        hB hD
      convert hsum.symm using 1
      ring

/-- The Frobenius powers in a rational presentation produce the expected
Cartier numerator. -/
theorem polynomialCartier_fraction_pow_mul {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (E F A B : k[X]) :
    polynomialCartier p (perfectFrobeniusEquiv p hperfect)
        ((E ^ p * A) * (F ^ p * B) ^ (p - 1)) =
      (E * F ^ (p - 1)) *
        polynomialCartier p (perfectFrobeniusEquiv p hperfect)
          (A * B ^ (p - 1)) := by
  have hF : (F ^ p) ^ (p - 1) = (F ^ (p - 1)) ^ p := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hinput :
      (E ^ p * A) * (F ^ p * B) ^ (p - 1) =
        (E * F ^ (p - 1)) ^ p * (A * B ^ (p - 1)) := by
    rw [mul_pow, mul_pow, hF]
    ring
  rw [hinput, polynomialCartier_pow_mul p hperfect]

/-- Multiplying two rational presentations multiplies their numerators and
denominators. -/
theorem ratFunc_mk_mul {k : Type*} [Field k]
    (A B C D : k[X]) :
    RatFunc.mk A B * RatFunc.mk C D = RatFunc.mk (A * C) (B * D) := by
  simp only [RatFunc.mk_eq_div, map_mul]
  exact div_mul_div_comm _ _ _ _

/-- A power of a rational presentation is represented by powers of its
numerator and denominator. -/
theorem ratFunc_mk_pow {k : Type*} [Field k]
    (A B : k[X]) (n : ℕ) :
    (RatFunc.mk A B) ^ n = RatFunc.mk (A ^ n) (B ^ n) := by
  simp only [RatFunc.mk_eq_div, map_pow, div_pow]

/-- Cartier on rational differentials is linear over Frobenius powers. -/
theorem rationalCartier_pow_mul {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p))
    (g r : RatFunc k) :
    rationalCartier p hperfect (g ^ p * r) =
      g * rationalCartier p hperfect r := by
  induction g using RatFunc.induction_on' with
  | _ E F hF =>
    induction r using RatFunc.induction_on' with
    | _ A B hB =>
      rw [ratFunc_mk_pow E F p, ratFunc_mk_mul,
        rationalCartier_mk p hperfect _ _ (mul_ne_zero (pow_ne_zero p hF) hB),
        rationalCartier_mk p hperfect _ _ hB,
        polynomialCartier_fraction_pow_mul p hperfect E F A B,
        ratFunc_mk_mul]
      have hp : 0 < p := (Fact.out : Nat.Prime p).pos
      have hpred : F ^ p = F ^ (p - 1) * F := by
        conv_lhs => rw [show p = p - 1 + 1 by omega]
        rw [pow_succ]
      apply (RatFunc.mk_eq_mk
        (mul_ne_zero (pow_ne_zero p hF) hB)
        (mul_ne_zero hF hB)).2
      rw [hpred]
      ring

end SptClassification
