/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMFiniteCuspClearing
public import SptClassification.ModularForms.HolomorphicProducts

/-!
# The discriminant in the finite level-six cusp charts

The determinant-six, determinant-three and determinant-eighteen charts
give respectively `6^6 Δ(6z)`, `3^6 Δ(3z)` and
`2^6 Δ(2z+1/3)` after the weight-twelve slash. The last factor of
three cancels because scaling a matrix does not change its fractional
action. This uses the full-level discriminant transformation and its
actual Euler expansion, with no new modular-form premise.
-/

public section

namespace SptClassification

open UpperHalfPlane

/-- The weight-twelve slash of the actual discriminant by an integral
unimodular matrix. -/
theorem discriminant_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (z : UpperHalfPlane) :
    ModularForm.discriminant (γ • z) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) z ^ 12 *
        ModularForm.discriminant z := by
  have h := congrFun (progressionIntegralSlash_discriminant_pow 1 γ) z
  simp only [progressionIntegralSlash_apply, mul_one, pow_one] at h
  rw [div_eq_iff (pow_ne_zero 12 (denom_ne_zero _ z))] at h
  simpa only [ModularForm.discriminant, mul_comm] using h

namespace FiniteLevelSixCusp

/-- The normalized weight-twelve slash of the actual discriminant in the
chosen rational chart. -/
noncomputable def discriminantSlash (c : FiniteLevelSixCusp)
    (z : UpperHalfPlane) : ℂ :=
  (c.chartMatrix.det : ℂ) ^ 6 *
    ModularForm.eta (c.approach z) ^ 24 /
      c.chartMatrix.denominator z ^ 12

/-- The explicit discriminant chart is its classical weight-twelve slash. -/
theorem discriminantSlash_eq_evenWeightSlash (c : FiniteLevelSixCusp)
    (z : UpperHalfPlane) :
    c.discriminantSlash z =
      PositiveCuspAction.evenWeightSlash 6 c.chartGL
        (fun w : UpperHalfPlane => ModularForm.discriminant w) z := by
  rw [PositiveCuspAction.evenWeightSlash_apply, c.chartGL_det,
    c.chartGL_denominator]
  simp only [discriminantSlash, ModularForm.discriminant, Nat.reduceMul]
  rw [c.chartGL_smul]
  rfl

/-- The germ in the width-one parameter after the matrix determinant is
included. The third cusp has the translation phase in its nome. -/
noncomputable def discriminantGerm (c : FiniteLevelSixCusp) (q : ℂ) : ℂ :=
  match c with
  | .zero => (6 : ℂ) ^ 6 * q ^ 6 * etaEulerProduct (q ^ 6) ^ 24
  | .half => (3 : ℂ) ^ 6 * q ^ 3 * etaEulerProduct (q ^ 3) ^ 24
  | .third => (2 : ℂ) ^ 6 *
      ((Function.Periodic.qParam 1 (1 / 3 : ℂ)) * q ^ 2) *
      etaEulerProduct ((Function.Periodic.qParam 1 (1 / 3 : ℂ)) * q ^ 2) ^ 24

/-- The inversion chart at zero is the discriminant of `6z`, with the
determinant-six normalization retained. -/
theorem discriminantSlash_zero (z : UpperHalfPlane) :
    discriminantSlash .zero z =
      (6 : ℂ) ^ 6 * ModularForm.discriminant
        ⟨6 * (z : ℂ), by
          simpa using mul_pos (by norm_num : (0 : ℝ) < 6) z.im_pos⟩ := by
  let w : UpperHalfPlane :=
    ⟨6 * (z : ℂ), by
      simpa using mul_pos (by norm_num : (0 : ℝ) < 6) z.im_pos⟩
  have hS : ((ModularGroup.S • w : UpperHalfPlane) : ℂ) =
      -1 / (6 * (z : ℂ)) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [w, one_div, neg_div]
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) w =
      6 * (z : ℂ) := by
    exact ModularGroup.denom_S w
  have hΔ := discriminant_smul ModularGroup.S w
  rw [hd] at hΔ
  change ModularForm.discriminant (ModularGroup.S • w) = _ at hΔ
  have hco : ModularForm.discriminant (ModularGroup.S • w) =
      ModularForm.eta (-1 / (6 * (z : ℂ))) ^ 24 := by
    simpa only [ModularForm.discriminant, hS]
  rw [hco] at hΔ
  simp only [discriminantSlash, chartMatrix_det, chartMatrix_denominator,
    approach_zero] at *
  change (6 : ℂ) ^ 6 *
      ModularForm.eta (-1 / (6 * (z : ℂ))) ^ 24 /
        (6 * (z : ℂ)) ^ 12 =
      (6 : ℂ) ^ 6 * ModularForm.discriminant w
  rw [hΔ]
  field_simp [z.ne_zero]

/-- The half chart is the lower-unipotent action on `3z`. -/
theorem discriminantSlash_half (z : UpperHalfPlane) :
    discriminantSlash .half z =
      (3 : ℂ) ^ 6 * ModularForm.discriminant (cuspHalfTriplePoint z) := by
  let w := cuspHalfTriplePoint z
  have hact : ((lowerUnipotent 2 • w : UpperHalfPlane) : ℂ) =
      cuspHalfApproach w := by
    rw [lowerUnipotent_apply, cuspHalfApproach_eq]
    simp only [w]
    ring
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ (lowerUnipotent 2)) w =
      6 * (z : ℂ) + 1 := by
    rw [lowerUnipotent_denom]
    simp only [w, cuspHalfTriplePoint_coe]
    ring
  have hΔ := discriminant_smul (lowerUnipotent 2) w
  rw [hd] at hΔ
  have hco : ModularForm.discriminant (lowerUnipotent 2 • w) =
      ModularForm.eta (cuspHalfApproach w) ^ 24 := by
    simpa only [ModularForm.discriminant, hact]
  rw [hco] at hΔ
  simp only [discriminantSlash, chartMatrix_det, chartMatrix_denominator,
    approach_half] at *
  change (3 : ℂ) ^ 6 * ModularForm.eta (cuspHalfApproach w) ^ 24 /
      (6 * (z : ℂ) + 1) ^ 12 =
        (3 : ℂ) ^ 6 * ModularForm.discriminant w
  rw [hΔ]
  have hden : (6 : ℂ) * (z : ℂ) + 1 ≠ 0 := by
    simpa only [chartMatrix_denominator] using
      (chartMatrix_denominator_ne_zero FiniteLevelSixCusp.half z)
  field_simp [hden]

/-- The third chart is the lower-unipotent action on `2z+1/3`.
The determinant-eighteen slash reduces to determinant two after the
scalar factor three is cancelled. -/
theorem discriminantSlash_third (z : UpperHalfPlane) :
    discriminantSlash .third z =
      (2 : ℂ) ^ 6 * ModularForm.discriminant
        ⟨2 * (z : ℂ) + 1 / 3, by
          simpa using mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos⟩ := by
  let w : UpperHalfPlane :=
    ⟨2 * (z : ℂ) + 1 / 3, by
      simpa using mul_pos (by norm_num : (0 : ℝ) < 2) z.im_pos⟩
  have hden : (6 : ℂ) * (z : ℂ) + 2 ≠ 0 := by
    have him : 0 < ((6 : ℂ) * (z : ℂ) + 2).im := by
      simpa using mul_pos (by norm_num : (0 : ℝ) < 6) z.im_pos
    intro hz
    simp [hz] at him
  have hden18 : (18 : ℂ) * (z : ℂ) + 6 ≠ 0 := by
    simpa only [chartMatrix_denominator] using
      (chartMatrix_denominator_ne_zero FiniteLevelSixCusp.third z)
  have hact : ((lowerUnipotent 3 • w : UpperHalfPlane) : ℂ) =
      cuspThirdApproach (cuspHalfTriplePoint z) := by
    rw [lowerUnipotent_apply, cuspThirdApproach_eq, cuspHalfTriplePoint_coe]
    change (2 * (z : ℂ) + 1 / 3) / (3 * (2 * (z : ℂ) + 1 / 3) + 1) =
      (2 * (3 * (z : ℂ)) + 1) / (6 * (3 * (z : ℂ) + 1))
    apply (div_eq_div_iff (by convert hden using 1 <;> ring)
      (by convert hden18 using 1 <;> ring)).2
    ring
  have hd : denom (Matrix.SpecialLinearGroup.mapGL ℝ (lowerUnipotent 3)) w =
      6 * (z : ℂ) + 2 := by
    rw [lowerUnipotent_denom]
    simp only [w]
    ring
  have hΔ := discriminant_smul (lowerUnipotent 3) w
  rw [hd] at hΔ
  have hco : ModularForm.discriminant (lowerUnipotent 3 • w) =
      ModularForm.eta (cuspThirdApproach (cuspHalfTriplePoint z)) ^ 24 := by
    simpa only [ModularForm.discriminant, hact]
  rw [hco] at hΔ
  simp only [discriminantSlash, chartMatrix_det, chartMatrix_denominator,
    approach_third] at *
  change (18 : ℂ) ^ 6 * ModularForm.eta
      (cuspThirdApproach (cuspHalfTriplePoint z)) ^ 24 /
        (18 * (z : ℂ) + 6) ^ 12 =
      (2 : ℂ) ^ 6 * ModularForm.discriminant w
  rw [hΔ]
  have hscale : (18 : ℂ) * (z : ℂ) + 6 =
      3 * (6 * (z : ℂ) + 2) := by ring
  rw [hscale]
  field_simp [hden]
  ring

/-- The three determinant-normalized discriminant slashes are represented
by their actual Euler germs in the chosen width-one nomes. -/
theorem discriminantGerm_qParam (c : FiniteLevelSixCusp)
    (z : UpperHalfPlane) :
    c.discriminantGerm (Function.Periodic.qParam 1 z) =
      c.discriminantSlash z := by
  let q := Function.Periodic.qParam 1 z
  cases c with
  | zero =>
      rw [discriminantSlash_zero,
        discriminant_eq_etaEulerProduct]
      have hq : Function.Periodic.qParam 1 (6 * (z : ℂ)) = q ^ 6 := by
        simpa [q] using qParam_nat_mul 6 (z : ℂ)
      rw [hq]
      simp only [discriminantGerm, q]
      ring
  | half =>
      rw [discriminantSlash_half,
        discriminant_eq_etaEulerProduct]
      have hq : Function.Periodic.qParam 1 (cuspHalfTriplePoint z) = q ^ 3 := by
        simpa [q, cuspHalfTriplePoint_coe] using qParam_nat_mul 3 (z : ℂ)
      rw [hq]
      simp only [discriminantGerm, q]
      ring
  | third =>
      rw [discriminantSlash_third,
        discriminant_eq_etaEulerProduct]
      have hq : Function.Periodic.qParam 1 (2 * (z : ℂ) + 1 / 3) =
          Function.Periodic.qParam 1 (1 / 3 : ℂ) * q ^ 2 := by
        calc
          _ = Function.Periodic.qParam 1 (1 / 3 : ℂ) *
              Function.Periodic.qParam 1 (2 * (z : ℂ)) := by
                rw [show (2 : ℂ) * z + 1 / 3 = 1 / 3 + 2 * z by ring]
                exact qParam_one_add_complex _ _
          _ = _ := by
            congr 1
            simpa [q] using qParam_nat_mul 2 (z : ℂ)
      rw [hq]
      simp only [discriminantGerm, q]
      ring

theorem discriminantGerm_zero (c : FiniteLevelSixCusp) :
    c.discriminantGerm 0 = 0 := by
  cases c <;> simp [discriminantGerm]

theorem analyticAt_discriminantGerm (c : FiniteLevelSixCusp) :
    AnalyticAt ℂ c.discriminantGerm 0 := by
  have hη : AnalyticAt ℂ etaEulerProduct 0 :=
    analyticAt_etaEulerProduct (q := 0) (by simp)
  cases c with
  | zero =>
      have hcomp : AnalyticAt ℂ (fun q : ℂ => etaEulerProduct (q ^ 6)) 0 := by
        simpa only [Function.comp_def, Pi.pow_apply, id_eq] using
          AnalyticAt.comp (f := fun q : ℂ => q ^ 6) (by simpa using hη)
            (analyticAt_id.pow 6)
      exact (analyticAt_const.mul (analyticAt_id.pow 6)).mul (hcomp.pow 24)
  | half =>
      have hcomp : AnalyticAt ℂ (fun q : ℂ => etaEulerProduct (q ^ 3)) 0 := by
        simpa only [Function.comp_def, Pi.pow_apply, id_eq] using
          AnalyticAt.comp (f := fun q : ℂ => q ^ 3) (by simpa using hη)
            (analyticAt_id.pow 3)
      exact (analyticAt_const.mul (analyticAt_id.pow 3)).mul (hcomp.pow 24)
  | third =>
      have hq : AnalyticAt ℂ
          (fun q : ℂ => Function.Periodic.qParam 1 (1 / 3 : ℂ) * q ^ 2) 0 :=
        analyticAt_const.mul (analyticAt_id.pow 2)
      have hcomp : AnalyticAt ℂ
          (fun q : ℂ => etaEulerProduct
            (Function.Periodic.qParam 1 (1 / 3 : ℂ) * q ^ 2)) 0 := by
        simpa only [Function.comp_def] using
          AnalyticAt.comp
            (f := fun q : ℂ => Function.Periodic.qParam 1 (1 / 3 : ℂ) * q ^ 2)
            (by simpa using hη) hq
      exact (analyticAt_const.mul hq).mul (hcomp.pow 24)

end FiniteLevelSixCusp
end SptClassification
