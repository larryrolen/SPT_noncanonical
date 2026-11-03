/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.WeilVector

/-!
# The finite Fourier transform of the distinguished Weil vector

For the discriminant group `ℤ/12ℤ`, the finite Fourier numerator with kernel
`z^(-rs)` sends `e₁-e₅-e₇+e₁₁` to its conductor-twelve character times
the associated Gauss numerator. This combinatorial identity is the finite
part of the `S` calculation in [rolenManuscript, lines 339–342]. The
signature phase and analytic eta multiplier are separate obligations.
-/

public section

namespace SptClassification
namespace Theta

/-- The group algebra Fourier sum before choosing a root of unity or a Weil phase. -/
@[expose]
def fourierNumerator (R : Type*) [CommRing R] (z : R)
    (f : ZMod 12 → R) (s : ZMod 12) : R :=
  ∑ r : ZMod 12, f r * z ^ (-(r * s)).val

/-- The finite Gauss numerator of the conductor-twelve vector. -/
def gaussNumerator (R : Type*) [CommRing R] (z : R) : R :=
  z ^ 11 - z ^ 7 - z ^ 5 + z

private theorem fourierNumerator_four_terms (R : Type*) [CommRing R]
    (z : R) (s : ZMod 12) :
    fourierNumerator R z (weilInputVectorAs R) s =
      z ^ (-(1 * s : ZMod 12)).val - z ^ (-(5 * s : ZMod 12)).val -
        z ^ (-(7 * s : ZMod 12)).val + z ^ (-(11 * s : ZMod 12)).val := by
  simp [fourierNumerator, weilInputVectorAs, weilInputVector, basisVector,
    Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    add_mul, sub_mul]

private theorem fourier_row (R : Type*) [CommRing R] (z : R) (s : ZMod 12)
    (a b c d : ℕ) (v : ℤ)
    (h : (-(1 * s : ZMod 12)).val = a ∧
      (-(5 * s : ZMod 12)).val = b ∧
      (-(7 * s : ZMod 12)).val = c ∧
      (-(11 * s : ZMod 12)).val = d ∧
      weilInputVector s = v)
    (hpoly : z ^ a - z ^ b - z ^ c + z ^ d =
      (v : R) * gaussNumerator R z) :
    fourierNumerator R z (weilInputVectorAs R) s =
      weilInputVectorAs R s * gaussNumerator R z := by
  rcases h with ⟨ha, hb, hc, hd, hv⟩
  rw [fourierNumerator_four_terms, ha, hb, hc, hd]
  simpa only [weilInputVectorAs, hv] using hpoly

/-- The coefficient vector is an eigenvector of the unnormalized finite Fourier
operator, with its Gauss numerator as eigenvalue. -/
theorem fourierNumerator_weilInputVector (R : Type*) [CommRing R] (z : R) :
    fourierNumerator R z (weilInputVectorAs R) =
      fun s => (weilInputVectorAs R s) * gaussNumerator R z := by
  funext s
  fin_cases s
  case «0» => exact fourier_row R z 0 0 0 0 0 0 (by decide +kernel) (by ring)
  case «1» => exact fourier_row R z 1 11 7 5 1 1 (by decide +kernel) (by
    simp [gaussNumerator])
  case «2» => exact fourier_row R z 2 10 2 10 2 0 (by decide +kernel) (by ring)
  case «3» => exact fourier_row R z 3 9 9 3 3 0 (by decide +kernel) (by ring)
  case «4» => exact fourier_row R z 4 8 4 8 4 0 (by decide +kernel) (by ring)
  case «5» => exact fourier_row R z 5 7 11 1 5 (-1) (by decide +kernel) (by
    simp [gaussNumerator]; ring)
  case «6» => exact fourier_row R z 6 6 6 6 6 0 (by decide +kernel) (by ring)
  case «7» => exact fourier_row R z 7 5 1 11 7 (-1) (by decide +kernel) (by
    simp [gaussNumerator]; ring)
  case «8» => exact fourier_row R z 8 4 8 4 8 0 (by decide +kernel) (by ring)
  case «9» => exact fourier_row R z 9 3 3 9 9 0 (by decide +kernel) (by ring)
  case «10» => exact fourier_row R z 10 2 10 2 10 0 (by decide +kernel) (by ring)
  case «11» => exact fourier_row R z 11 1 5 7 11 1 (by decide +kernel) (by
    simp [gaussNumerator]; ring)

/-- At the twelfth root used by the negative discriminant pairing, the
conductor-twelve Gauss numerator is the positive square root of twelve. -/
theorem gaussNumerator_exp_neg_pi_div_six :
    gaussNumerator ℂ (Complex.exp (-(Real.pi / 6) * Complex.I)) =
      (Real.sqrt 12 : ℂ) := by
  let z : ℂ := Complex.exp (-(Real.pi / 6) * Complex.I)
  let w : ℂ := Complex.exp ((Real.pi / 6) * Complex.I)
  have hz6 : z ^ 6 = -1 := by
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_neg_pi_mul_I using 1
    congr 1
    ring
  have hzw : z * w = 1 := by
    dsimp [z, w]
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  have hz5 : z ^ 5 = -w := by
    calc
      z ^ 5 = z ^ 5 * (z * w) := by rw [hzw, mul_one]
      _ = z ^ 6 * w := by ring
      _ = -w := by rw [hz6]; ring
  have hz7 : z ^ 7 = -z := by
    calc
      z ^ 7 = z * z ^ 6 := by ring
      _ = -z := by rw [hz6]; ring
  have hz11 : z ^ 11 = w := by
    calc
      z ^ 11 = z ^ 5 * z ^ 6 := by ring
      _ = w := by rw [hz5, hz6]; ring
  have hsum : z + w = (Real.sqrt 3 : ℂ) := by
    dsimp [z, w]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    have harg : (Real.pi : ℂ) / 6 = ((Real.pi / 6 : ℝ) : ℂ) := by norm_num
    rw [harg, Complex.cos_neg, Complex.sin_neg]
    norm_cast
    rw [Real.cos_pi_div_six, Real.sin_pi_div_six]
    push_cast
    ring
  have hsqrt : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [show (12 : ℝ) = 4 * 3 by norm_num,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  change gaussNumerator ℂ z = (Real.sqrt 12 : ℂ)
  rw [gaussNumerator, hz11, hz7, hz5]
  rw [hsqrt]
  push_cast
  linear_combination 2 * hsum

/-- The conjugate twelfth root has the same real Gauss numerator. -/
theorem gaussNumerator_exp_pos_pi_div_six :
    gaussNumerator ℂ (Complex.exp ((Real.pi / 6) * Complex.I)) =
      (Real.sqrt 12 : ℂ) := by
  have hconj :
      (starRingEnd ℂ) (Complex.exp (-(Real.pi / 6) * Complex.I)) =
        Complex.exp ((Real.pi / 6) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
    rw [map_ofNat]
  have h := congrArg (starRingEnd ℂ) gaussNumerator_exp_neg_pi_div_six
  simp only [gaussNumerator, map_add, map_sub, map_pow, hconj,
    Complex.conj_ofReal] at h
  exact h

end Theta
end SptClassification
