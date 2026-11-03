/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansion
public import SptClassification.ModularForms.EtaUnipotent
public import Mathlib.Tactic.Positivity

/-!
# The zero cusp of the level-six eta quotient

The Fricke substitution `z ↦ -1/(6z)` exchanges the infinity and zero cusps.
We calculate its effect on the actual eta quotient, following the coordinate
normalization of [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

/-- Positive real scaling commutes with the principal complex square root in
the upper half-plane. -/
theorem complex_sqrt_pos_mul_upper (r : ℝ) (hr : 0 < r) (z : UpperHalfPlane) :
    ((r : ℂ) * z).sqrt = (Real.sqrt r : ℂ) * (z : ℂ).sqrt := by
  symm
  apply eq_complex_sqrt_of_sq_eq
  · rw [mul_pow, complex_sqrt_sq]
    rw [← Complex.ofReal_pow, Real.sq_sqrt hr.le]
  · have hs := (complex_sqrt_re_im_pos z.im_pos).1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    exact mul_pos (Real.sqrt_pos.2 hr) hs

/-- The positive square-root multiplier of the Fricke substitution is `72`. -/
theorem levelSix_sqrt_multiplier :
    ((Real.sqrt 6 : ℂ) ^ 5 * (Real.sqrt 2 : ℂ)) /
      (Real.sqrt 3 : ℂ) = 72 := by
  have hroot : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by
    have hs : (Real.sqrt 6 * Real.sqrt 2) ^ 2 = (2 * Real.sqrt 3) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num),
        Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
      norm_num
    nlinarith [Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3,
      mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg 2)]
  have hreal : Real.sqrt 6 ^ 5 * Real.sqrt 2 = 72 * Real.sqrt 3 := by
    calc
      _ = (Real.sqrt 6 ^ 2) ^ 2 * (Real.sqrt 6 * Real.sqrt 2) := by ring
      _ = (6 : ℝ) ^ 2 * (2 * Real.sqrt 3) := by
        rw [Real.sq_sqrt (by norm_num), hroot]
      _ = 72 * Real.sqrt 3 := by ring
  have hc : (Real.sqrt 6 : ℂ) ^ 5 * (Real.sqrt 2 : ℂ) =
      72 * (Real.sqrt 3 : ℂ) := by exact_mod_cast hreal
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)))
  rw [hc, mul_div_cancel_right₀ _ h3]

/-- The Fricke involution exchanges the zero and infinity cusps with the exact
normalization `t ↦ 72/t`. -/
theorem levelSixEtaQuotient_fricke_six (z : UpperHalfPlane) :
    levelSixEtaQuotient (-1 / (6 * (z : ℂ))) =
      72 / levelSixEtaQuotient z := by
  let κ : ℂ := Complex.I.sqrt⁻¹
  let w : ℂ := (z : ℂ).sqrt
  have hη (r : ℕ) (hr : 0 < r) :
      ModularForm.eta (-1 / ((r : ℂ) * z)) =
        κ * (Real.sqrt r : ℂ) * w * ModularForm.eta ((r : ℂ) * z) := by
    have hrz : 0 < (((r : ℂ) * z).im) := by
      simpa using mul_pos (show (0 : ℝ) < r by exact_mod_cast hr) z.im_pos
    have hs : ((r : ℂ) * z).sqrt = (Real.sqrt r : ℂ) * w := by
      simpa [w] using complex_sqrt_pos_mul_upper (r : ℝ)
        (by exact_mod_cast hr) z
    rw [eta_neg_inv hrz, hs]
    dsimp [κ]
    ring
  have h1 := hη 1 (by norm_num)
  have h2 := hη 2 (by norm_num)
  have h3 := hη 3 (by norm_num)
  have h6 := hη 6 (by norm_num)
  norm_num only [Nat.cast_one, one_mul, Real.sqrt_one, Complex.ofReal_one,
    one_mul] at h1
  norm_num only [Nat.cast_ofNat] at h2 h3 h6
  have harg2 : (2 : ℂ) * (-1 / (6 * z)) = -1 / (3 * z) := by
    field_simp [z.ne_zero]
    ring
  have harg3 : (3 : ℂ) * (-1 / (6 * z)) = -1 / (2 * z) := by
    field_simp [z.ne_zero]
    ring
  have harg6 : (6 : ℂ) * (-1 / (6 * z)) = -1 / z := by
    field_simp [z.ne_zero]
  have hw : w ≠ 0 := by
    intro he
    have hs := complex_sqrt_sq (z : ℂ)
    change w ^ 2 = (z : ℂ) at hs
    rw [he, zero_pow (by decide)] at hs
    exact z.ne_zero hs.symm
  have hκ : κ ≠ 0 := by
    dsimp [κ]
    apply inv_ne_zero
    intro he
    have hs := complex_sqrt_sq Complex.I
    rw [he, zero_pow (by decide)] at hs
    exact Complex.I_ne_zero hs.symm
  have hη1 := eta_pos_mul_ne_zero 1 (by norm_num) z
  have hη2 := eta_pos_mul_ne_zero 2 (by norm_num) z
  have hη3 := eta_pos_mul_ne_zero 3 (by norm_num) z
  have hη6 := eta_pos_mul_ne_zero 6 (by norm_num) z
  rw [levelSixEtaQuotient_eq]
  rw [harg2, harg3, harg6, h6, h3, h2, h1]
  have hsqrt := levelSix_sqrt_multiplier
  field_simp [hw, hκ, hη1, hη2, hη3, hη6]
  have h3root : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)))
  have hfactor : (Real.sqrt 6 : ℂ) ^ 5 * (Real.sqrt 2 : ℂ) =
      (Real.sqrt 3 : ℂ) * 72 := by
    calc
      _ = 72 * (Real.sqrt 3 : ℂ) := (div_eq_iff h3root).mp hsqrt
      _ = _ := by ring
  calc
    _ = ((Real.sqrt 6 : ℂ) ^ 5 * (Real.sqrt 2 : ℂ) *
        (ModularForm.eta (6 * z) ^ 5 * ModularForm.eta (2 * z))) /
        (ModularForm.eta (3 * z) * ModularForm.eta z ^ 5) := by ring_nf
    _ = ((Real.sqrt 3 : ℂ) * 72 *
        (ModularForm.eta (6 * z) ^ 5 * ModularForm.eta (2 * z))) /
        (ModularForm.eta (3 * z) * ModularForm.eta z ^ 5) := by rw [hfactor]
    _ = _ := by
      rw [levelSixEtaQuotient_eq]
      simp only [mul_comm (z : ℂ) (6 : ℂ), mul_comm (z : ℂ) (2 : ℂ),
        mul_comm (z : ℂ) (3 : ℂ), div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]
      ring

/-- The Fricke transform has a normalized zero: its quotient by the infinity
nome is `72` divided by the Euler unit. -/
theorem levelSixEtaQuotient_fricke_six_div_qParam (z : UpperHalfPlane) :
    levelSixEtaQuotient (-1 / (6 * (z : ℂ))) /
        Function.Periodic.qParam 1 z =
      72 / levelSixEulerUnit (Function.Periodic.qParam 1 z) := by
  rw [levelSixEtaQuotient_fricke_six]
  rw [← qParam_mul_levelSixEtaQuotient]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- On approach to the zero cusp through the Fricke substitution, `t/q`
tends to the exact leading coefficient `72`. -/
theorem tendsto_levelSixEtaQuotient_fricke_six_div_qParam
    {α : Type*} {l : Filter α} (z : α → UpperHalfPlane)
    (hz : Filter.Tendsto
      (fun a => Function.Periodic.qParam 1 (z a : ℂ)) l (nhds 0)) :
    Filter.Tendsto
      (fun a => levelSixEtaQuotient (-1 / (6 * (z a : ℂ))) /
        Function.Periodic.qParam 1 (z a : ℂ)) l (nhds 72) := by
  have hu : Filter.Tendsto
      (fun a => levelSixEulerUnit (Function.Periodic.qParam 1 (z a : ℂ)))
      l (nhds 1) := by
    simpa only [Function.comp_def, levelSixEulerUnit_zero] using
      continuousAt_levelSixEulerUnit_zero.tendsto.comp hz
  have ht := (tendsto_const_nhds.div hu (by norm_num : (1 : ℂ) ≠ 0) :
    Filter.Tendsto
      ((fun _ : α => (72 : ℂ)) /
        fun a => levelSixEulerUnit (Function.Periodic.qParam 1 (z a : ℂ)))
      l (nhds (72 / 1)))
  change Filter.Tendsto
    (fun a => (72 : ℂ) /
      levelSixEulerUnit (Function.Periodic.qParam 1 (z a : ℂ)))
    l (nhds (72 / 1)) at ht
  simpa only [levelSixEtaQuotient_fricke_six_div_qParam, div_one] using ht

end SptClassification
