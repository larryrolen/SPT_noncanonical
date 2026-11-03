/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaUnipotent

/-! # The cusp-zero parabolic law of the level-six eta quotient -/

public section

namespace SptClassification

/-- The exact eta quotient is invariant under the parabolic matrix `[1,0;6,1]`. -/
theorem levelSixEtaQuotient_cusp_zero (z : UpperHalfPlane) :
    levelSixEtaQuotient ((z : ℂ) / (6 * z + 1)) = levelSixEtaQuotient z := by
  have h1 := eta_scaled_lower_unipotent z 1 (by norm_num) 6
  have h2 := eta_scaled_lower_unipotent z 2 (by norm_num) 3
  have h3 := eta_scaled_lower_unipotent z 3 (by norm_num) 2
  have h6 := eta_scaled_lower_unipotent z 6 (by norm_num) 1
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Int.cast_one, Int.cast_ofNat,
    mul_one, one_mul, show (3 : ℂ) * 2 = 6 by norm_num,
    show (2 : ℂ) * 3 = 6 by norm_num] at h1 h2 h3 h6
  have hden : (6 : ℂ) * z + 1 ≠ 0 := by
    simpa using z.linear_ne_zero (cd := ![6, 1]) (by
      intro h
      have he := congrFun h 1
      norm_num at he)
  have hroot : ((6 : ℂ) * z + 1).sqrt ≠ 0 := by
    intro h
    have hs := complex_sqrt_sq ((6 : ℂ) * z + 1)
    rw [h, zero_pow (by decide)] at hs
    exact hden hs.symm
  have hphase :
      (Complex.exp (-Real.pi * Complex.I * 6 / 12) ^ 5 *
        Complex.exp (-Real.pi * Complex.I * 2 / 12)) /
      (Complex.exp (-Real.pi * Complex.I * 3 / 12) *
        Complex.exp (-Real.pi * Complex.I / 12) ^ 5) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub]
    norm_num only [Nat.cast_ofNat]
    have he : (5 : ℂ) * (-Real.pi * Complex.I * 6 / 12) +
        (-Real.pi * Complex.I * 2 / 12) -
        (-Real.pi * Complex.I * 3 / 12 + 5 * (-Real.pi * Complex.I / 12)) =
        -(2 * Real.pi * Complex.I) := by ring
    rw [he, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  rw [levelSixEtaQuotient_eq]
  rw [h1, h2, h3, h6]
  calc
    _ = ((Complex.exp (-Real.pi * Complex.I * 6 / 12) ^ 5 *
        Complex.exp (-Real.pi * Complex.I * 2 / 12)) /
      (Complex.exp (-Real.pi * Complex.I * 3 / 12) *
        Complex.exp (-Real.pi * Complex.I / 12) ^ 5)) *
      (ModularForm.eta z ^ 5 * ModularForm.eta (3 * z) /
        (ModularForm.eta (2 * z) * ModularForm.eta (6 * z) ^ 5)) := by
      field_simp [hroot]
    _ = _ := by rw [hphase, one_mul, levelSixEtaQuotient_eq]

end SptClassification
