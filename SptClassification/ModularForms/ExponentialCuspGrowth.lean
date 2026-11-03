/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CuspHeightBounds
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Tactic.Positivity

/-!
# Algebra of exponential estimates in cusp strips

These estimates concern actual functions on the upper half-plane. They are
stable under the operations in the normalized representative of
[rolenManuscript, §2, (2.5)].
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- Exponential growth, uniformly on a fixed bounded real strip and above
some nonnegative height. -/
def HasExponentialGrowthOnStrip (f : UpperHalfPlane → ℂ) (R : ℝ) : Prop :=
  ∃ C A Y : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ 0 ≤ Y ∧
    ∀ τ : UpperHalfPlane, |τ.re| ≤ R → Y ≤ τ.im →
      ‖f τ‖ ≤ C * Real.exp (A * τ.im)

namespace HasExponentialGrowthOnStrip

variable {f g : UpperHalfPlane → ℂ} {R : ℝ}

/-- Extract constants for use in analytic cusp criteria. -/
theorem exists_bounds (hf : HasExponentialGrowthOnStrip f R) :
    ∃ C A Y : ℝ, 0 ≤ C ∧ 0 ≤ A ∧ 0 ≤ Y ∧
      ∀ τ : UpperHalfPlane, |τ.re| ≤ R → Y ≤ τ.im →
        ‖f τ‖ ≤ C * Real.exp (A * τ.im) := hf

theorem const (c : ℂ) : HasExponentialGrowthOnStrip (fun _ => c) R := by
  exact ⟨‖c‖, 0, 0, norm_nonneg _, le_rfl, le_rfl, by simp⟩

theorem of_bounded (hf : IsBoundedAtImInfty f) :
    HasExponentialGrowthOnStrip f R := by
  obtain ⟨C, Y, h⟩ := isBoundedAtImInfty_iff.mp hf
  refine ⟨max C 0, 0, max Y 0, le_max_right _ _, le_rfl, le_max_right _ _, ?_⟩
  intro τ _ hy
  simpa using (h τ ((le_max_left _ _).trans hy)).trans (le_max_left C 0)

theorem congr (hf : HasExponentialGrowthOnStrip f R) (h : ∀ τ, f τ = g τ) :
    HasExponentialGrowthOnStrip g R := by
  simpa only [funext h] using hf

theorem neg (hf : HasExponentialGrowthOnStrip f R) :
    HasExponentialGrowthOnStrip (fun τ => -f τ) R := by
  simpa only [HasExponentialGrowthOnStrip, norm_neg] using hf

theorem add (hf : HasExponentialGrowthOnStrip f R)
    (hg : HasExponentialGrowthOnStrip g R) :
    HasExponentialGrowthOnStrip (fun τ => f τ + g τ) R := by
  obtain ⟨C, A, Y, hC, hA, hY, hf⟩ := hf
  obtain ⟨D, B, Z, hD, hB, hZ, hg⟩ := hg
  refine ⟨C + D, max A B, max Y Z, add_nonneg hC hD,
    hA.trans (le_max_left _ _), hY.trans (le_max_left _ _), ?_⟩
  intro τ hx hy
  have hfa := hf τ hx ((le_max_left _ _).trans hy)
  have hga := hg τ hx ((le_max_right _ _).trans hy)
  have ha : Real.exp (A * τ.im) ≤ Real.exp (max A B * τ.im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) τ.im_pos.le)
  have hb : Real.exp (B * τ.im) ≤ Real.exp (max A B * τ.im) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) τ.im_pos.le)
  calc
    ‖f τ + g τ‖ ≤ ‖f τ‖ + ‖g τ‖ := norm_add_le _ _
    _ ≤ C * Real.exp (max A B * τ.im) + D * Real.exp (max A B * τ.im) :=
      add_le_add (hfa.trans (mul_le_mul_of_nonneg_left ha hC))
        (hga.trans (mul_le_mul_of_nonneg_left hb hD))
    _ = (C + D) * Real.exp (max A B * τ.im) := by ring

theorem sub (hf : HasExponentialGrowthOnStrip f R)
    (hg : HasExponentialGrowthOnStrip g R) :
    HasExponentialGrowthOnStrip (fun τ => f τ - g τ) R := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem mul (hf : HasExponentialGrowthOnStrip f R)
    (hg : HasExponentialGrowthOnStrip g R) :
    HasExponentialGrowthOnStrip (fun τ => f τ * g τ) R := by
  obtain ⟨C, A, Y, hC, hA, hY, hf⟩ := hf
  obtain ⟨D, B, Z, hD, hB, hZ, hg⟩ := hg
  refine ⟨C * D, A + B, max Y Z, mul_nonneg hC hD, add_nonneg hA hB,
    hY.trans (le_max_left _ _), ?_⟩
  intro τ hx hy
  calc
    ‖f τ * g τ‖ = ‖f τ‖ * ‖g τ‖ := norm_mul _ _
    _ ≤ (C * Real.exp (A * τ.im)) * (D * Real.exp (B * τ.im)) :=
      mul_le_mul (hf τ hx ((le_max_left _ _).trans hy))
        (hg τ hx ((le_max_right _ _).trans hy)) (norm_nonneg _)
        (mul_nonneg hC (Real.exp_pos _).le)
    _ = (C * D) * Real.exp ((A + B) * τ.im) := by rw [add_mul, Real.exp_add]; ring

theorem pow (hf : HasExponentialGrowthOnStrip f R) (n : ℕ) :
    HasExponentialGrowthOnStrip (fun τ => f τ ^ n) R := by
  induction n with
  | zero => simpa using (const (R := R) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

theorem div_const (hf : HasExponentialGrowthOnStrip f R) (c : ℂ) :
    HasExponentialGrowthOnStrip (fun τ => f τ / c) R := by
  simpa only [div_eq_mul_inv] using hf.mul (const c⁻¹)

theorem of_height_bound {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hf : ∀ τ : UpperHalfPlane,
      ‖f τ‖ ≤ C * Real.exp (A * (τ.im + 1 / τ.im)))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hR : 0 ≤ R) :
    HasExponentialGrowthOnStrip (fun τ => f (γ • τ)) R := by
  obtain ⟨B, hB, h⟩ := cusp_exp_bound_of_height_bound f hC hA hf γ R hR
  exact ⟨C, B, 1, hC, hB, by norm_num, h⟩

/-- Dividing by an integral slash denominator cannot increase the norm above
height one. -/
theorem div_denom_pow (hf : HasExponentialGrowthOnStrip f R)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (n : ℕ) :
    HasExponentialGrowthOnStrip
      (fun τ => f τ / denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ n) R := by
  obtain ⟨C, A, Y, hC, hA, hY, hf⟩ := hf
  refine ⟨C, A, max Y 1, hC, hA, hY.trans (le_max_left _ _), ?_⟩
  intro τ hx hy
  have hd : 1 ≤ ‖denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ‖ := by
    have hs := one_le_normSq_integral_denom γ τ ((le_max_right _ _).trans hy)
    rw [Complex.normSq_eq_norm_sq] at hs
    nlinarith [norm_nonneg (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ)]
  calc
    ‖f τ / denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ n‖ =
        ‖f τ‖ / ‖denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ‖ ^ n := by
      rw [norm_div, norm_pow]
    _ ≤ ‖f τ‖ := div_le_self (norm_nonneg _) (one_le_pow₀ hd)
    _ ≤ C * Real.exp (A * τ.im) := hf τ hx ((le_max_left _ _).trans hy)

/-- Every fixed integral automorphy denominator has exponential growth on
bounded real strips. -/
theorem denom (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hR : 0 ≤ R) :
    HasExponentialGrowthOnStrip
      (fun τ => UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) R := by
  let K : ℝ := |(γ 1 0 : ℝ)| * (R + 1) + |(γ 1 1 : ℝ)|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, 1, 1, hK, by norm_num, by norm_num, ?_⟩
  intro τ hx hy
  have ht : ‖(τ : ℂ)‖ ≤ R + τ.im := by
    exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
      simpa only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_pos τ.im_pos]
        using add_le_add hx le_rfl)
  have hnorm : ‖UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ‖ ≤
      |(γ 1 0 : ℝ)| * (R + τ.im) + |(γ 1 1 : ℝ)| := by
    change ‖(γ 1 0 : ℂ) * (τ : ℂ) + (γ 1 1 : ℂ)‖ ≤ _
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    simp only [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact add_le_add (mul_le_mul_of_nonneg_left ht (abs_nonneg _)) le_rfl
  have hpoly : |(γ 1 0 : ℝ)| * (R + τ.im) + |(γ 1 1 : ℝ)| ≤ K * τ.im := by
    have hRscale := mul_le_mul_of_nonneg_left hy hR
    have hdscale := mul_le_mul_of_nonneg_left hy (abs_nonneg (γ 1 1 : ℝ))
    have hcscale := mul_le_mul_of_nonneg_left hRscale (abs_nonneg (γ 1 0 : ℝ))
    dsimp [K]
    nlinarith
  have he : τ.im ≤ Real.exp τ.im := by linarith [Real.add_one_le_exp τ.im]
  simpa only [one_mul] using hnorm.trans (hpoly.trans (mul_le_mul_of_nonneg_left he hK))

end HasExponentialGrowthOnStrip

end SptClassification
