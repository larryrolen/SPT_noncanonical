/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.ModularForms.Derivative

/-!
# The negative half-integral Serre derivative

The derivative in [rolenManuscript, §2, (2.5)] can be handled by
integer-weight equivariance: multiply by a nonvanishing theta function,
and use its fourth power to compute the transformation of its derivative.
-/

public section

namespace SptClassification

open UpperHalfPlane Derivative
open scoped Manifold ModularForm MatrixGroups

/-- The Serre product rule for a fourth power, including fractional weights. -/
theorem serreDerivative_fourth_power (k : ℂ) (F : UpperHalfPlane → ℂ)
    (hF : MDiff F) :
    serreDerivative (4 * k) (F ^ 4) = 4 * F ^ 3 * serreDerivative k F := by
  funext τ
  simp only [serreDerivative_apply, normalizedDerivOfComplex_pow F 4 hF,
    Pi.mul_apply, Pi.pow_apply, Pi.ofNat_apply, Pi.natCast_apply]
  ring

/-- Integer-weight equivariance with a constant character value. -/
theorem serreDerivative_map_of_integer_weight (k : ℤ)
    (F : UpperHalfPlane → ℂ) (hF : MDiff F)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (χ : ℂ)
    (htrans : ∀ τ : UpperHalfPlane, F (γ • τ) =
      χ * (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ k * F τ)
    (τ : UpperHalfPlane) :
    serreDerivative k F (γ • τ) =
      χ * (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ (k + 2) *
        serreDerivative k F τ := by
  have hslash : F ∣[k] γ = χ • F := by
    funext z
    rw [ModularForm.SL_slash_apply, htrans]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hd := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) z
    simp only [zpow_neg]
    field_simp
    change χ * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) z ^ k * F z =
      χ * F z * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) z ^ k
    ring
  have h := congrFun (serreDerivative_slash_equivariant (k := k) hF (γ := γ)) τ
  rw [hslash, serreDerivative_smul _ _ hF] at h
  simp only [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul] at h
  have hd := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
  change serreDerivative k F (γ • τ) *
    (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ (-(k + 2)) =
    χ * serreDerivative k F τ at h
  have hz := zpow_ne_zero (k + 2) hd
  rw [zpow_neg] at h
  change serreDerivative k F (γ • τ) /
    (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ (k + 2) =
    χ * serreDerivative k F τ at h
  have he := (div_eq_iff hz).mp h
  simpa only [mul_assoc, mul_comm, mul_left_comm] using he

/-- A negative half-weight function has a weight `3/2` Serre derivative.
The auxiliary theta function must be nonvanishing; the function being
differentiated may have zeros. Integer-weight equivariance of the product
and of the fourth power supplies the entire argument. -/
theorem serreDerivative_map_of_negative_half_weight
    (F T : UpperHalfPlane → ℂ) (hF : MDiff F) (hT : MDiff T)
    (hTzero : ∀ τ, T τ ≠ 0)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (χ : ℂ)
    (j : UpperHalfPlane → ℂ)
    (hTheta : ∀ τ, T (γ • τ) = j τ * T τ)
    (hfour : ∀ τ, j τ ^ 4 =
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ 2)
    (htrans : ∀ τ, F (γ • τ) = χ / j τ * F τ)
    (τ : UpperHalfPlane) :
    serreDerivative (-1 / 2) F (γ • τ) =
      χ * j τ ^ 3 * serreDerivative (-1 / 2) F τ := by
  have hj (z : UpperHalfPlane) : j z ≠ 0 := by
    intro hz
    exact hTzero (γ • z) (by rw [hTheta, hz, zero_mul])
  have hpow : ∀ z : UpperHalfPlane, (T ^ 4) (γ • z) =
      (1 : ℂ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) z ^ (2 : ℤ) *
        (T ^ 4) z := by
    intro z
    simp only [Pi.pow_apply, hTheta, mul_pow, hfour, zpow_ofNat, one_mul]
  have hprod : ∀ z : UpperHalfPlane, (F * T) (γ • z) =
      χ * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) z ^ (0 : ℤ) *
        (F * T) z := by
    intro z
    simp only [Pi.mul_apply, htrans, hTheta, zpow_zero, mul_one]
    field_simp [hj z]
  have h4 := serreDerivative_map_of_integer_weight 2 (T ^ 4) (hT.pow 4)
    γ 1 hpow τ
  have h0 := serreDerivative_map_of_integer_weight 0 (F * T) (hF.mul hT)
    γ χ hprod τ
  have hp := serreDerivative_fourth_power (1 / 2) T hT
  norm_num only at hp
  norm_num only [Int.cast_ofNat] at h4
  rw [hp] at h4
  have hm := serreDerivative_mul (-1 / 2) (1 / 2) hF hT
  norm_num only at hm
  norm_num only [Int.cast_zero] at h0
  rw [hm] at h0
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.add_apply, Pi.ofNat_apply,
    hTheta, htrans] at h4 h0
  norm_num only [Int.cast_ofNat, Int.cast_zero, zpow_ofNat, zero_add,
    one_mul] at h4 h0
  have hd4 : denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ 4 = j τ ^ 8 := by
    calc
      _ = (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ 2) ^ 2 := by ring
      _ = _ := by rw [← hfour]; ring
  rw [hd4] at h4
  rw [← hfour] at h0
  have hDT : serreDerivative (1 / 2) T (γ • τ) =
      j τ ^ 5 * serreDerivative (1 / 2) T τ := by
    apply mul_left_cancel₀ (show 4 * j τ ^ 3 * T τ ^ 3 ≠ 0 by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (hj τ)))
        (pow_ne_zero _ (hTzero τ)))
    linear_combination h4
  rw [hDT] at h0
  apply mul_left_cancel₀ (mul_ne_zero (hj τ) (hTzero τ))
  field_simp at h0
  simp only [neg_div] at ⊢
  linear_combination h0

end SptClassification
