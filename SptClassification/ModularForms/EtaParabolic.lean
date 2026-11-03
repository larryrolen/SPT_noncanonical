/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaUnipotent

/-! # Eta under conjugated integral translations -/

public section

namespace SptClassification

/-- The integral lower-unipotent matrix. -/
def lowerUnipotent (n : ℤ) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 0; n, 1], by norm_num [Matrix.det_fin_two]⟩

theorem lowerUnipotent_denom (n : ℤ) (z : UpperHalfPlane) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ (lowerUnipotent n)) z =
      (n : ℂ) * z + 1 := by
  have hm : ((Matrix.SpecialLinearGroup.mapGL ℝ (lowerUnipotent n) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; (n : ℝ), 1] := by
    simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [lowerUnipotent, Matrix.map_apply]
  simp [UpperHalfPlane.denom, hm]

theorem lowerUnipotent_apply (n : ℤ) (z : UpperHalfPlane) :
    (↑(lowerUnipotent n • z : UpperHalfPlane) : ℂ) = (z : ℂ) / ((n : ℂ) * z + 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [lowerUnipotent]

theorem eta_lowerUnipotent_action (n : ℤ) (z : UpperHalfPlane) :
    ModularForm.eta (↑(lowerUnipotent n • z : UpperHalfPlane) : ℂ) =
      Complex.exp (-Real.pi * Complex.I * n / 12) * ((n : ℂ) * z + 1).sqrt * ModularForm.eta z := by
  rw [lowerUnipotent_apply]
  exact eta_lower_unipotent z n

/-- The parabolic at the rational cusp `1/a`, formed by actual matrix actions. -/
noncomputable def reciprocalCuspParabolic (a b : ℤ) (z : UpperHalfPlane) : UpperHalfPlane :=
  lowerUnipotent a • ((b : ℝ) +ᵥ (lowerUnipotent (-a) • z))

theorem reciprocalCuspParabolic_apply (a b : ℤ) (z : UpperHalfPlane) :
    (reciprocalCuspParabolic a b z : ℂ) =
      ((1 - (a : ℂ) * b) * z + b) / (1 + (a : ℂ) * b - (a : ℂ) ^ 2 * b * z) := by
  have hinner : (-(a : ℂ)) * z + 1 ≠ 0 := by
    simpa using z.linear_ne_zero (cd := ![(-a : ℝ), 1]) (by
      intro h
      have he := congrFun h 1
      norm_num at he)
  have hinner' : 1 - (a : ℂ) * z ≠ 0 := by convert hinner using 1; ring
  have houter : 1 + (a : ℂ) * b - (a : ℂ) ^ 2 * b * z ≠ 0 := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    have hlin := z.linear_ne_zero (cd := ![(-(a : ℝ) ^ 2 * b), 1 + (a : ℝ) * b]) (by
      intro h
      have he := congrFun h 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at he
      have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
      have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      exact (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 haR)) hbR) he)
    convert hlin using 1
    push_cast
    ring
  unfold reciprocalCuspParabolic
  rw [lowerUnipotent_apply, UpperHalfPlane.coe_vadd, lowerUnipotent_apply]
  push_cast
  have hdenRewrite : (a : ℂ) * (b + (z : ℂ) / (-(a : ℂ) * z + 1)) + 1 =
      (1 + (a : ℂ) * b - (a : ℂ) ^ 2 * b * z) / (-(a : ℂ) * z + 1) := by
    ring_nf at hinner hinner' ⊢
    field_simp [hinner, hinner']
    ring
  rw [hdenRewrite, div_div_eq_mul_div]
  ring_nf at hinner hinner' houter ⊢
  field_simp [hinner, hinner', houter]
  ring

/-- The exact eta multiplier at a reciprocal rational cusp. -/
theorem eta_reciprocalCuspParabolic (a b : ℤ) (ha : 0 < a) (z : UpperHalfPlane) :
    ModularForm.eta (reciprocalCuspParabolic a b z : ℂ) =
      Complex.exp (Real.pi * Complex.I * b / 12) *
        (1 + (a : ℂ) * b - (a : ℂ) ^ 2 * b * z).sqrt * ModularForm.eta z := by
  let u := lowerUnipotent (-a) • z
  let v := (b : ℝ) +ᵥ u
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hfirst : ((-(a : ℂ)) * z + 1).im < 0 := by
    simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.intCast_re, Complex.intCast_im, neg_zero, zero_mul, add_zero, Complex.one_im]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos har) z.im_pos
  have hsecond : 0 < ((a : ℂ) * (v : ℂ) + 1).im := by
    simpa using mul_pos har v.im_pos
  have hinner : (-(a : ℂ)) * z + 1 ≠ 0 := by
    intro h
    simp only [h, Complex.zero_im, lt_self_iff_false] at hfirst
  have hinner' : 1 - (a : ℂ) * z ≠ 0 := by convert hinner using 1; ring
  have hproduct : ((-(a : ℂ)) * z + 1) * ((a : ℂ) * (v : ℂ) + 1) =
      1 + (a : ℂ) * b - (a : ℂ) ^ 2 * b * z := by
    change ((-(a : ℂ)) * z + 1) * ((a : ℂ) * ((b : ℂ) + (u : ℂ)) + 1) = _
    dsimp only [u]
    rw [lowerUnipotent_apply]
    push_cast
    ring_nf at hinner hinner' ⊢
    field_simp [hinner, hinner']
    ring
  have hroot := complex_sqrt_mul_opposite hfirst hsecond
  rw [hproduct] at hroot
  have htranslation : ModularForm.eta (v : ℂ) =
      Complex.exp (Real.pi * Complex.I * b / 12) * ModularForm.eta (u : ℂ) := by
    simpa only [v, UpperHalfPlane.coe_vadd, Complex.ofReal_intCast, add_comm] using
      eta_add_int (u : ℂ) b
  have hphases : Complex.exp (-Real.pi * Complex.I * a / 12) *
      Complex.exp (-Real.pi * Complex.I * (-a : ℤ) / 12) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    push_cast
    ring
  simp only [Int.cast_neg] at hphases
  change ModularForm.eta (↑(lowerUnipotent a • v : UpperHalfPlane) : ℂ) = _
  rw [eta_lowerUnipotent_action, htranslation]
  dsimp only [u]
  rw [eta_lowerUnipotent_action]
  simp only [Int.cast_neg]
  calc
    _ = (Complex.exp (-Real.pi * Complex.I * a / 12) *
        Complex.exp (-Real.pi * Complex.I * (-(a : ℂ)) / 12)) *
      Complex.exp (Real.pi * Complex.I * b / 12) *
      (((-(a : ℂ)) * z + 1).sqrt * ((a : ℂ) * (v : ℂ) + 1).sqrt) * ModularForm.eta z := by ring
    _ = _ := by rw [hphases, hroot, one_mul]

/-- Translating a cusp conjugates the linear square-root factor and preserves
its constant eta multiplier. -/
theorem eta_translation_conjugate (s c d : ℤ) (f : UpperHalfPlane → UpperHalfPlane)
    (phase : ℂ)
    (h : ∀ w : UpperHalfPlane, ModularForm.eta (f w : ℂ) =
      phase * ((c : ℂ) * w + d).sqrt * ModularForm.eta w)
    (z : UpperHalfPlane) :
    ModularForm.eta (↑((s : ℝ) +ᵥ f ((-s : ℝ) +ᵥ z)) : ℂ) =
      phase * ((c : ℂ) * z + d - (c : ℂ) * s).sqrt * ModularForm.eta z := by
  let w : UpperHalfPlane := (-s : ℝ) +ᵥ z
  have houter : ModularForm.eta (↑((s : ℝ) +ᵥ f w) : ℂ) =
      Complex.exp (Real.pi * Complex.I * s / 12) * ModularForm.eta (f w : ℂ) := by
    simpa only [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast, add_comm] using
      eta_add_int (f w : ℂ) s
  have hinner : ModularForm.eta (w : ℂ) =
      Complex.exp (Real.pi * Complex.I * (-s : ℤ) / 12) * ModularForm.eta z := by
    simpa only [w, UpperHalfPlane.coe_vadd, Int.cast_neg, Complex.ofReal_neg,
      Complex.ofReal_intCast, add_comm] using eta_add_int (z : ℂ) (-s)
  have hphases : Complex.exp (Real.pi * Complex.I * s / 12) *
      Complex.exp (Real.pi * Complex.I * (-s : ℤ) / 12) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    push_cast
    ring
  have hfactor : (c : ℂ) * (w : ℂ) + d = (c : ℂ) * z + d - (c : ℂ) * s := by
    change (c : ℂ) * (↑(-s : ℝ) + (z : ℂ)) + d = _
    push_cast
    ring
  change ModularForm.eta (↑((s : ℝ) +ᵥ f w) : ℂ) = _
  rw [houter, h, hinner, hfactor]
  calc
    _ = (Complex.exp (Real.pi * Complex.I * s / 12) *
        Complex.exp (Real.pi * Complex.I * (-s : ℤ) / 12)) *
      (phase * ((c : ℂ) * z + d - (c : ℂ) * s).sqrt * ModularForm.eta z) := by ring
    _ = _ := by rw [hphases, one_mul]

end SptClassification
