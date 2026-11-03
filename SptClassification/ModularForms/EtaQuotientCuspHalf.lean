/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaParabolic

/-! # The cusp-one-half parabolic law of the level-six eta quotient -/

public section

namespace SptClassification

/-- The eta multiplier of the cusp-one-half parabolic. -/
theorem eta_cusp_half (z : UpperHalfPlane) :
    ModularForm.eta ((-5 * (z : ℂ) + 3) / (-12 * z + 7)) =
      Complex.exp (Real.pi * Complex.I * 3 / 12) * (-12 * (z : ℂ) + 7).sqrt * ModularForm.eta z := by
  have h := eta_reciprocalCuspParabolic 2 3 (by norm_num) z
  rw [reciprocalCuspParabolic_apply] at h
  norm_num at h
  convert h using 1 <;> ring_nf

/-- The eta multiplier at twice the cusp-one-half variable. -/
theorem eta_twice_cusp_half (z : UpperHalfPlane) :
    ModularForm.eta (2 * ((-5 * (z : ℂ) + 3) / (-12 * z + 7))) =
      Complex.exp (Real.pi * Complex.I * 6 / 12) * (-12 * (z : ℂ) + 7).sqrt * ModularForm.eta (2 * z) := by
  let w : UpperHalfPlane := ⟨2 * (z : ℂ), by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos⟩
  have h := eta_reciprocalCuspParabolic 1 6 (by norm_num) w
  rw [reciprocalCuspParabolic_apply] at h
  dsimp only [w, UpperHalfPlane.coe_mk] at h
  convert h using 1 <;> ring_nf

/-- The eta multiplier at three times the cusp-one-half variable. -/
theorem eta_thrice_cusp_half (z : UpperHalfPlane) :
    ModularForm.eta (3 * ((-5 * (z : ℂ) + 3) / (-12 * z + 7))) =
      Complex.exp (Real.pi * Complex.I / 12) * (-12 * (z : ℂ) + 7).sqrt * ModularForm.eta (3 * z) := by
  let w : UpperHalfPlane := ⟨3 * (z : ℂ), by simpa using mul_pos (by norm_num : (0 : ℝ) < 3) z.im_pos⟩
  have hf (v : UpperHalfPlane) : ModularForm.eta (reciprocalCuspParabolic 2 1 v : ℂ) =
      Complex.exp (Real.pi * Complex.I / 12) * ((-4 : ℂ) * v + 3).sqrt * ModularForm.eta v := by
    have h := eta_reciprocalCuspParabolic 2 1 (by norm_num) v
    convert h using 1
    ring_nf
  have h := eta_translation_conjugate 1 (-4) 3 (reciprocalCuspParabolic 2 1)
    (Complex.exp (Real.pi * Complex.I / 12)) (by intro v; simpa using hf v) w
  rw [UpperHalfPlane.coe_vadd, reciprocalCuspParabolic_apply, UpperHalfPlane.coe_vadd] at h
  norm_num only [Int.cast_one, Int.cast_ofNat, Int.cast_neg, Complex.ofReal_one,
    Complex.ofReal_neg, mul_one] at h
  have hden : (-12 : ℂ) * z + 7 ≠ 0 := by
    simpa using z.linear_ne_zero (cd := ![-12, 7]) (by
      intro h
      have he := congrFun h 1
      norm_num at he)
  dsimp only [w, UpperHalfPlane.coe_mk] at h
  convert h using 1
  · congr 1
    ring_nf at hden ⊢
    field_simp [hden]
    ring
  · ring_nf

/-- The eta multiplier at six times the cusp-one-half variable. -/
theorem eta_six_cusp_half (z : UpperHalfPlane) :
    ModularForm.eta (6 * ((-5 * (z : ℂ) + 3) / (-12 * z + 7))) =
      Complex.exp (Real.pi * Complex.I * 2 / 12) * (-12 * (z : ℂ) + 7).sqrt * ModularForm.eta (6 * z) := by
  let w : UpperHalfPlane := ⟨6 * (z : ℂ), by simpa using mul_pos (by norm_num : (0 : ℝ) < 6) z.im_pos⟩
  have hf (v : UpperHalfPlane) : ModularForm.eta (↑(lowerUnipotent (-2) • v : UpperHalfPlane) : ℂ) =
      Complex.exp (Real.pi * Complex.I * 2 / 12) * ((-2 : ℂ) * v + 1).sqrt * ModularForm.eta v := by
    have h := eta_lowerUnipotent_action (-2) v
    convert h using 1
    push_cast
    ring_nf
  have h := eta_translation_conjugate 3 (-2) 1 (fun v => lowerUnipotent (-2) • v)
    (Complex.exp (Real.pi * Complex.I * 2 / 12)) (by intro v; simpa using hf v) w
  rw [UpperHalfPlane.coe_vadd, lowerUnipotent_apply, UpperHalfPlane.coe_vadd] at h
  norm_num only [Int.cast_one, Int.cast_ofNat, Int.cast_neg, Complex.ofReal_ofNat,
    Complex.ofReal_neg, mul_one] at h
  have hden : (-12 : ℂ) * z + 7 ≠ 0 := by
    simpa using z.linear_ne_zero (cd := ![-12, 7]) (by
      intro h
      have he := congrFun h 1
      norm_num at he)
  dsimp only [w, UpperHalfPlane.coe_mk] at h
  convert h using 1
  · congr 1
    ring_nf at hden ⊢
    field_simp [hden]
    ring
  · ring_nf

/-- The exact quotient is invariant under the parabolic matrix `[-5,3;-12,7]`. -/
theorem levelSixEtaQuotient_cusp_half (z : UpperHalfPlane) :
    levelSixEtaQuotient ((-5 * (z : ℂ) + 3) / (-12 * z + 7)) = levelSixEtaQuotient z := by
  have hden : (-12 : ℂ) * z + 7 ≠ 0 := by
    simpa using z.linear_ne_zero (cd := ![-12, 7]) (by
      intro h
      have he := congrFun h 1
      norm_num at he)
  have hroot : (-12 * (z : ℂ) + 7).sqrt ≠ 0 := by
    intro h
    have hs := complex_sqrt_sq (-12 * (z : ℂ) + 7)
    rw [h, zero_pow (by decide)] at hs
    exact hden hs.symm
  have hphase :
      (Complex.exp (Real.pi * Complex.I * 3 / 12) ^ 5 * Complex.exp (Real.pi * Complex.I / 12)) /
      (Complex.exp (Real.pi * Complex.I * 6 / 12) * Complex.exp (Real.pi * Complex.I * 2 / 12) ^ 5) = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_sub]
    convert Complex.exp_zero using 1
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [levelSixEtaQuotient_eq]
  rw [eta_cusp_half, eta_twice_cusp_half, eta_thrice_cusp_half, eta_six_cusp_half]
  calc
    _ = ((Complex.exp (Real.pi * Complex.I * 3 / 12) ^ 5 * Complex.exp (Real.pi * Complex.I / 12)) /
        (Complex.exp (Real.pi * Complex.I * 6 / 12) * Complex.exp (Real.pi * Complex.I * 2 / 12) ^ 5)) *
      (ModularForm.eta z ^ 5 * ModularForm.eta (3 * z) /
        (ModularForm.eta (2 * z) * ModularForm.eta (6 * z) ^ 5)) := by
      ring_nf at hroot ⊢
      field_simp [hroot]
    _ = _ := by rw [hphase, one_mul, levelSixEtaQuotient_eq]

end SptClassification
