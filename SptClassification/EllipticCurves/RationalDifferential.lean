/- Assembled by AxiomProver. -/

module

public import SptClassification.EllipticCurves.RationalCartier

/-!
# Exact rational differentials and Cartier

The quotient rule defines the formal differential of a rational function over
its coefficient field. Its independence from a fraction presentation, together
with the characteristic-`p` derivative identity below, shows that rational
Cartier annihilates exact differentials. See [silverman2009, Chapter V].
-/

public section

namespace SptClassification

open Polynomial

/-- The quotient-rule numerator of a rational differential. -/
@[expose] noncomputable def rationalDifferentialNumerator {k : Type*} [Field k]
    (A B : k[X]) : k[X] := derivative A * B - A * derivative B

/-- The quotient-rule differential is independent of the chosen polynomial
fraction presentation. -/
theorem rationalDifferential_fraction_cross {k : Type*} [Field k]
    (A B C D : k[X]) (h : A * D = C * B) :
    rationalDifferentialNumerator A B * D ^ 2 =
      rationalDifferentialNumerator C D * B ^ 2 := by
  have hd := congrArg derivative h
  simp only [derivative_mul] at hd
  dsimp [rationalDifferentialNumerator]
  linear_combination (B * D) * hd -
    (derivative B * D + B * derivative D) * h

/-- The formal derivative of a rational function, expressed by the quotient
rule on every presentation. -/
@[expose] noncomputable def rationalDifferential {k : Type*} [Field k]
    (r : RatFunc k) : RatFunc k :=
  r.liftOn
    (fun A B => RatFunc.mk (rationalDifferentialNumerator A B) (B ^ 2))
    (by
      intro A B C D hB hD h
      have hB0 : B ≠ 0 := nonZeroDivisors.ne_zero hB
      have hD0 : D ≠ 0 := nonZeroDivisors.ne_zero hD
      apply (RatFunc.mk_eq_mk (pow_ne_zero 2 hB0) (pow_ne_zero 2 hD0)).2
      exact rationalDifferential_fraction_cross A B C D
        (by simpa only [mul_comm] using h))

/-- Quotient rule for the rational differential of `A/B`. -/
theorem rationalDifferential_mk {k : Type*} [Field k]
    (A B : k[X]) (hB : B ≠ 0) :
    rationalDifferential (RatFunc.mk A B) =
      RatFunc.mk (rationalDifferentialNumerator A B) (B ^ 2) := by
  unfold rationalDifferential
  rw [RatFunc.mk_eq_localization_mk A hB]
  simp only [RatFunc.liftOn_ofFractionRing_mk]

/-- The rational differential extends the polynomial derivative. -/
theorem rationalDifferential_mk_one {k : Type*} [Field k] (A : k[X]) :
    rationalDifferential (RatFunc.mk A 1) = RatFunc.mk (derivative A) 1 := by
  rw [rationalDifferential_mk A 1 one_ne_zero]
  simp [rationalDifferentialNumerator]

/-- The quotient-rule differential is additive on rational functions. -/
theorem rationalDifferential_add {k : Type*} [Field k]
    (r s : RatFunc k) :
    rationalDifferential (r + s) =
      rationalDifferential r + rationalDifferential s := by
  induction r using RatFunc.induction_on' with
  | _ A B hB =>
    induction s using RatFunc.induction_on' with
    | _ C D hD =>
      rw [ratFunc_mk_add A B C D hB hD,
        rationalDifferential_mk _ _ (mul_ne_zero hB hD),
        rationalDifferential_mk A B hB,
        rationalDifferential_mk C D hD]
      have hsum := ratFunc_mk_add
        (rationalDifferentialNumerator A B) (B ^ 2)
        (rationalDifferentialNumerator C D) (D ^ 2)
        (pow_ne_zero 2 hB) (pow_ne_zero 2 hD)
      convert hsum.symm using 1
      simp only [rationalDifferentialNumerator, derivative_add, derivative_mul]
      ring

/-- The quotient-rule differential satisfies Leibniz's rule. -/
theorem rationalDifferential_mul {k : Type*} [Field k]
    (r s : RatFunc k) :
    rationalDifferential (r * s) =
      rationalDifferential r * s + r * rationalDifferential s := by
  induction r using RatFunc.induction_on' with
  | _ A B hB =>
    induction s using RatFunc.induction_on' with
    | _ C D hD =>
      rw [ratFunc_mk_mul A B C D,
        rationalDifferential_mk _ _ (mul_ne_zero hB hD),
        rationalDifferential_mk A B hB,
        rationalDifferential_mk C D hD,
        ratFunc_mk_mul, ratFunc_mk_mul]
      rw [ratFunc_mk_add _ _ _ _
        (mul_ne_zero (pow_ne_zero 2 hB) hD)
        (mul_ne_zero hB (pow_ne_zero 2 hD))]
      apply (RatFunc.mk_eq_mk
        (pow_ne_zero 2 (mul_ne_zero hB hD))
        (mul_ne_zero
          (mul_ne_zero (pow_ne_zero 2 hB) hD)
          (mul_ne_zero hB (pow_ne_zero 2 hD)))).2
      dsimp [rationalDifferentialNumerator]
      simp only [derivative_mul]
      ring

/-- In characteristic `p`, the numerator used for Cartier on an exact
rational differential is itself an exact polynomial differential. -/
theorem derivative_fraction_cartierNumerator {k : Type*} [Field k]
    (p : ℕ) (hp : 0 < p) (hchar : (p : k) = 0) (A B : k[X]) :
    rationalDifferentialNumerator A B * (B ^ 2) ^ (p - 1) =
      derivative (A * B ^ (2 * p - 1)) := by
  have hpow : B ^ (2 * p - 1) = B ^ (2 * p - 2) * B := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow' : (B ^ 2) ^ (p - 1) = B ^ (2 * p - 2) := by
    rw [← pow_mul]
    congr 1
    omega
  have hpred : 2 * p - 1 - 1 = 2 * p - 2 := by omega
  have hcast : ((2 * p - 1 : ℕ) : k) = -1 := by
    have hnum : ((2 * p - 1 : ℕ) : k) + 1 = (2 : k) * (p : k) := by
      calc
        ((2 * p - 1 : ℕ) : k) + 1 = ((2 * p - 1 + 1 : ℕ) : k) := by
          push_cast
          ring
        _ = (2 : k) * (p : k) := by
          rw [show 2 * p - 1 + 1 = 2 * p by omega]
          push_cast
          ring
    rw [hchar, mul_zero] at hnum
    exact eq_neg_of_add_eq_zero_left hnum
  rw [derivative_mul, derivative_pow]
  rw [hcast, hpow, hpow', hpred]
  dsimp [rationalDifferentialNumerator]
  simp only [map_neg, map_one]
  ring

/-- Cartier annihilates exact rational differentials. -/
theorem rationalCartier_rationalDifferential {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hperfect : Function.Bijective (frobenius k p)) (r : RatFunc k) :
    rationalCartier p hperfect (rationalDifferential r) = 0 := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have hchar : (p : k) = 0 := by
    exact (CharP.cast_eq_zero_iff k p p).2 (dvd_refl p)
  induction r using RatFunc.induction_on' with
  | _ A B hB =>
      rw [rationalDifferential_mk A B hB]
      rw [rationalCartier_mk p hperfect _ _ (pow_ne_zero 2 hB)]
      rw [derivative_fraction_cartierNumerator p hp hchar A B]
      rw [polynomialCartier_derivative p hp hchar]
      simp

end SptClassification
