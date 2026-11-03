/- Assembled by AxiomProver. -/

module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Height bounds in an integral cusp coordinate

On a bounded real strip above height one, the height of `γτ` and its reciprocal
are bounded by a constant times the height of `τ`. This transfers estimates for
the actual generating series to the cusp coordinates used in
[rolenManuscript, §2].
-/

public section

namespace SptClassification

open UpperHalfPlane

theorem normSq_integral_denom (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) :
    Complex.normSq (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) =
      ((γ 1 0 : ℝ) * τ.re + (γ 1 1 : ℝ)) ^ 2 +
        ((γ 1 0 : ℝ) * τ.im) ^ 2 := by
  change Complex.normSq ((γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)) = _
  simp [Complex.normSq, pow_two]
  <;> ring

/-- Above height one an integral determinant-one denominator has norm at
least one. Integrality, rather than a uniform bound for real matrices, is used. -/
theorem one_le_normSq_integral_denom (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    1 ≤ Complex.normSq (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) := by
  rw [normSq_integral_denom]
  by_cases hc : γ 1 0 = 0
  · have hd : γ 1 1 ≠ 0 := by
      intro hd
      have hn := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
      apply hn
      change (γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ) = 0
      simp [hc, hd]
    have hd2 : (1 : ℝ) ≤ (γ 1 1 : ℝ) ^ 2 := by
      exact_mod_cast (show (1 : ℤ) ≤ (γ 1 1) ^ 2 by nlinarith [sq_pos_of_ne_zero hd])
    simpa [hc] using hd2
  · have hc2 : (1 : ℝ) ≤ (γ 1 0 : ℝ) ^ 2 := by
      exact_mod_cast (show (1 : ℤ) ≤ (γ 1 0) ^ 2 by nlinarith [sq_pos_of_ne_zero hc])
    have hy2 : 1 ≤ τ.im ^ 2 := by nlinarith
    have hh := mul_le_mul hc2 hy2 (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg _)
    nlinarith [sq_nonneg ((γ 1 0 : ℝ) * τ.re + (γ 1 1 : ℝ))]

/-- Both height directions are controlled on any fixed horizontal strip. -/
theorem exists_cusp_height_bound (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 < B ∧ ∀ τ : UpperHalfPlane,
      |τ.re| ≤ R → 1 ≤ τ.im →
      (γ • τ).im + 1 / (γ • τ).im ≤ B * τ.im := by
  let K : ℝ := (|(γ 1 0 : ℝ)| * R + |(γ 1 1 : ℝ)|) ^ 2 + (γ 1 0 : ℝ) ^ 2
  have hK : 0 ≤ K := add_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨1 + K, by linarith, ?_⟩
  intro τ hx hy
  let D := Complex.normSq (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ)
  have hD : 0 < D := normSq_denom_pos _ τ.im_ne_zero
  have hD1 : 1 ≤ D := one_le_normSq_integral_denom γ τ hy
  have hlin : |(γ 1 0 : ℝ) * τ.re + (γ 1 1 : ℝ)| ≤
      |(γ 1 0 : ℝ)| * R + |(γ 1 1 : ℝ)| := by
    exact (abs_add_le _ _).trans (by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _)) le_rfl)
  have hlin2 := sq_le_sq₀ (abs_nonneg _) (add_nonneg (mul_nonneg (abs_nonneg _) hR)
    (abs_nonneg _)) |>.mpr hlin
  rw [sq_abs] at hlin2
  have hscale : (|(γ 1 0 : ℝ)| * R + |(γ 1 1 : ℝ)|) ^ 2 ≤
      (|(γ 1 0 : ℝ)| * R + |(γ 1 1 : ℝ)|) ^ 2 * τ.im ^ 2 := by
    have : 1 ≤ τ.im ^ 2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left this
      (sq_nonneg (|(γ 1 0 : ℝ)| * R + |(γ 1 1 : ℝ)|))
  have hDupper : D ≤ K * τ.im ^ 2 := by
    dsimp [D, K]
    rw [normSq_integral_denom]
    nlinarith
  have him : (γ • τ).im = τ.im / D := ModularGroup.im_smul_eq_div_normSq γ τ
  rw [him]
  have hfirst : τ.im / D ≤ τ.im := (div_le_self τ.im_pos.le hD1)
  have hsecond : 1 / (τ.im / D) ≤ K * τ.im := by
    rw [one_div_div]
    apply (div_le_iff₀ τ.im_pos).mpr
    nlinarith [hDupper]
  nlinarith

/-- A global exponential estimate in `y + 1/y` becomes an exponential estimate
in each integral cusp coordinate, uniformly on a bounded real strip. -/
theorem cusp_exp_bound_of_height_bound
    (f : UpperHalfPlane → ℂ) {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hf : ∀ τ : UpperHalfPlane,
      ‖f τ‖ ≤ C * Real.exp (A * (τ.im + 1 / τ.im)))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : UpperHalfPlane,
      |τ.re| ≤ R → 1 ≤ τ.im → ‖f (γ • τ)‖ ≤ C * Real.exp (B * τ.im) := by
  obtain ⟨B, hB, hbound⟩ := exists_cusp_height_bound γ R hR
  refine ⟨A * B, mul_nonneg hA hB.le, ?_⟩
  intro τ hx hy
  apply (hf (γ • τ)).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  simpa [mul_assoc] using mul_le_mul_of_nonneg_left (hbound τ hx hy) hA

end SptClassification
