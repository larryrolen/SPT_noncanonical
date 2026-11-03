/- Assembled by AxiomProver. -/

module

public import SptClassification.Analysis.ComplexSquareRoot
public import SptClassification.ModularForms.EtaTranslation
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Tactic.FieldSimp

/-!
# The lower-unipotent transformation of eta

Composing inversion, integer translation, and inversion gives the exact
principal-square-root multiplier for `z ↦ z / (nz + 1)`.
-/

public section

namespace SptClassification

/-- The inversion law of the actual eta function in pointwise form. -/
theorem eta_neg_inv {z : ℂ} (hz : 0 < z.im) :
    ModularForm.eta (-1 / z) = Complex.I.sqrt⁻¹ * z.sqrt * ModularForm.eta z := by
  simpa only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_assoc] using
    ModularForm.eta_comp_eq_csqrt_I_inv hz

/-- The principal-branch eta multiplier for every integral lower-unipotent matrix. -/
theorem eta_lower_unipotent (z : UpperHalfPlane) (n : ℤ) :
    ModularForm.eta ((z : ℂ) / ((n : ℂ) * z + 1)) =
      Complex.exp (-Real.pi * Complex.I * n / 12) *
        ((n : ℂ) * z + 1).sqrt * ModularForm.eta z := by
  let w : ℂ := -1 / (z : ℂ) - n
  have hinv : 0 < (-1 / (z : ℂ)).im := by
    simp only [neg_div, one_div, Complex.neg_im, Complex.inv_im, neg_neg]
    exact div_pos z.im_pos (Complex.normSq_pos.mpr z.ne_zero)
  have hw : 0 < w.im := by simpa [w] using hinv
  have hden : (n : ℂ) * z + 1 ≠ 0 := by
    simpa using z.linear_ne_zero (cd := ![(n : ℝ), 1]) (by
      intro h
      have he := congrFun h 1
      norm_num at he)
  have hwform : -1 / w = (z : ℂ) / ((n : ℂ) * z + 1) := by
    have hw0 : w ≠ 0 := by intro h; simp only [h, Complex.zero_im, lt_self_iff_false] at hw
    apply (div_eq_div_iff hw0 hden).mpr
    dsimp [w]
    field_simp [z.ne_zero]
    ring
  have hwproduct : -w * (z : ℂ) = (n : ℂ) * z + 1 := by
    dsimp [w]
    field_simp [z.ne_zero]
    ring
  have hroot := complex_sqrt_inversion_product z.im_pos hw
  rw [hwproduct] at hroot
  have hphase : ModularForm.eta w =
      Complex.exp (-Real.pi * Complex.I * n / 12) * ModularForm.eta (-1 / (z : ℂ)) := by
    simpa only [w, Int.cast_neg, sub_eq_add_neg, mul_neg, neg_mul] using
      eta_add_int (-1 / (z : ℂ)) (-n)
  have hIsq : (Complex.I.sqrt⁻¹) ^ 2 = -Complex.I := by
    rw [inv_pow, complex_sqrt_sq]
    simp
  rw [← hwform, eta_neg_inv hw, hphase, eta_neg_inv z.im_pos]
  calc
    _ = Complex.exp (-Real.pi * Complex.I * n / 12) *
        ((Complex.I.sqrt⁻¹) ^ 2 * w.sqrt * (z : ℂ).sqrt) * ModularForm.eta z := by ring
    _ = _ := by rw [hIsq, hroot]

/-- Rescaling the variable in the lower-unipotent eta formula. -/
theorem eta_scaled_lower_unipotent (z : UpperHalfPlane) (r : ℕ) (hr : 0 < r) (n : ℤ) :
    ModularForm.eta ((r : ℂ) * ((z : ℂ) / ((n : ℂ) * r * z + 1))) =
      Complex.exp (-Real.pi * Complex.I * n / 12) *
        ((n : ℂ) * r * z + 1).sqrt * ModularForm.eta ((r : ℂ) * z) := by
  let rz : UpperHalfPlane := ⟨(r : ℂ) * z, by
    simpa using mul_pos (show (0 : ℝ) < r by exact_mod_cast hr) z.im_pos⟩
  simpa only [rz, UpperHalfPlane.coe_mk, mul_div_assoc, mul_assoc] using eta_lower_unipotent rz n

end SptClassification
