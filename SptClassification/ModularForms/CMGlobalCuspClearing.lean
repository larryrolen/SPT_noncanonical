/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.DiscriminantPoleClearing
public import SptClassification.ModularForms.LevelSixCuspCriterion
public import SptClassification.ModularForms.CMHighCuspClearing
public import SptClassification.ModularForms.CMShimuraClearedObstruction
public import SptClassification.ModularForms.PositiveCuspAction
public import SptClassification.ModularForms.CMAnalyticTransformation

/-!
# Global CM clearing from finite cusp bounds

The actual removable CM extension, multiplied by `Delta^(8h)`, gives a
holomorphic modular form of weight `96h+4`. Its infinity bound and integral
Fourier row follow from the same lift's convergent series. Only the three
finite cusp bounds remain explicit inputs to this construction.
[rolenManuscript, Section 4, proof of prop:obstruction]
-/

public section

namespace SptClassification

open Filter UpperHalfPlane OnePoint
open scoped Topology MatrixGroups

/-- A bound for the explicit discriminant/CM/lift product in a positive
determinant chart also bounds the actual removable extension at that cusp. -/
theorem cmCleared_boundedAt_of_representative (D : ℤ) [Fact (D < 0)]
    (J : ℂ → ℂ) (g : GL (Fin 2) ℝ) (hg : 0 < g.det.val)
    (hanalytic : AnalyticOnNhd ℂ (cmPoleClearedFunction D J) {w | 0 < w.im})
    (hgerm : ∀ z : UpperHalfPlane,
      (fun w => cmPoleFactor D w ^ 2 * J w) =ᶠ[𝓝[≠] (z : ℂ)]
        cmPoleClearedFunction D J)
    (hbound : IsBoundedAtImInfty
      (PositiveCuspAction.evenWeightSlash (48 * formClassNumber D + 2) g
        (fun z : UpperHalfPlane =>
          ModularForm.discriminant z ^ (8 * formClassNumber D) *
            (cmPoleFactor D z ^ 2 * J z)))) :
    (g • ∞).IsBoundedAt
      (fun z : UpperHalfPlane =>
        ModularForm.discriminant z ^ (8 * formClassNumber D) *
          cmPoleClearedFunction D J z)
      ((96 * formClassNumber D + 4 : ℕ) : ℤ) := by
  have hw : 96 * formClassNumber D + 4 =
      2 * (48 * formClassNumber D + 2) := by omega
  rw [hw]
  apply PositiveCuspAction.boundedAt_of_punctured_germ _ g hg
    (fun z : UpperHalfPlane =>
      ModularForm.discriminant z ^ (8 * formClassNumber D) *
        (cmPoleFactor D z ^ 2 * J z))
  · have hcont : Continuous (fun z : UpperHalfPlane => cmPoleClearedFunction D J z) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact (hanalytic z z.im_pos).continuousAt.comp
        UpperHalfPlane.continuous_coe.continuousAt
    exact (CuspForm.discriminant.holo'.continuous.pow _).mul hcont
  · intro z
    filter_upwards [upperHalfPlane_punctured_germ z (hgerm z)] with w hw
    exact congrArg (fun t => ModularForm.discriminant w ^
      (8 * formClassNumber D) * t) hw
  · exact hbound

/-- Construct the global cleared form from the analytic interior extension
and its three finite cusp bounds. The function equality holds everywhere
in the upper half-plane, including the removable CM points. -/
theorem cmClearedModularForm_of_finite_bounds (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hmod : d % 24 = 23) (hsq : Squarefree d)
    (J : ℂ → ℂ) (Y : ℝ)
    (hanalytic : AnalyticOnNhd ℂ
      (cmPoleClearedFunction (-(d : ℤ)) J) {w | 0 < w.im})
    (htrans : ∀ (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane),
      cmPoleClearedFunction (-(d : ℤ)) J
        ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ
          (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ 4 *
            cmPoleClearedFunction (-(d : ℤ)) J z)
    (hgerm : ∀ z : UpperHalfPlane,
      (fun w => cmPoleFactor (-(d : ℤ)) w ^ 2 * J w) =ᶠ[𝓝[≠] (z : ℂ)]
        cmPoleClearedFunction (-(d : ℤ)) J)
    (hsum : ∀ z : UpperHalfPlane, Y < z.im →
      HasSum (fun n : ℕ =>
        ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
          Function.Periodic.qParam 1 z ^ n) (J z))
    (hfinite : ∀ c ∈ ({0, 1 / 2, 1 / 3} : Set ℝ),
      (↑c : OnePoint ℝ).IsBoundedAt
        (fun z : UpperHalfPlane =>
          ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
            cmPoleClearedFunction (-(d : ℤ)) J z)
        ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ)) :
    ∃ F : ModularForm ((CongruenceSubgroup.Gamma0 6).map
        (Matrix.SpecialLinearGroup.mapGL ℝ))
        ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ),
      ∀ z : UpperHalfPlane,
        F z = ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
          cmPoleClearedFunction (-(d : ℤ)) J z := by
  have hw : 12 * (8 * formClassNumber (-(d : ℤ))) + 4 =
      96 * formClassNumber (-(d : ℤ)) + 4 := by omega
  rw [← hw] at hfinite ⊢
  let f := discriminantPoleClearing (cmPoleClearedFunction (-(d : ℤ)) J)
    (8 * formClassNumber (-(d : ℤ))) htrans
  have hhol := discriminantPoleClearing_holomorphic
    (cmPoleClearedFunction (-(d : ℤ)) J)
    (8 * formClassNumber (-(d : ℤ))) htrans hanalytic
  have hinfty := principalCMShimuraLift_cleared_bounded_at_infty d hmod hsq
    J Y hanalytic hgerm hsum
  have hf : (f : UpperHalfPlane → ℂ) = fun z =>
      ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
        cmPoleClearedFunction (-(d : ℤ)) J z := by
    funext z
    exact discriminantPoleClearing_apply _ _ htrans z
  have hb : ∀ c ∈ ({0, 1 / 2, 1 / 3} : Set ℝ),
      (↑c : OnePoint ℝ).IsBoundedAt f
        ((12 * (8 * formClassNumber (-(d : ℤ))) + 4 : ℕ) : ℤ) := by
    simpa only [hf] using hfinite
  have hi : IsBoundedAtImInfty f := by simpa only [hf] using hinfty
  refine ⟨LevelSixCuspCriterion.modularFormOfFourCusps f hhol hi
    (hb 0 (by simp)) (hb (1 / 2) (by simp)) (hb (1 / 3) (by simp)), ?_⟩
  intro z
  simpa only [LevelSixCuspCriterion.modularFormOfFourCusps_apply] using congrFun hf z

/-- The manuscript obstruction follows once the finite cusp bounds for the
same principal lift have been established. The global modular form, exact
Fourier row, residue specialization and Hasse argument are all constructed. -/
theorem character_obstruction_of_finite_cusp_bounds
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (sign : ℤ) (hsign : sign = 1 ∨ sign = -1)
    (d : ℕ) [Fact (-(d : ℤ) < 0)] (hd : 0 < d) (hsq : Squarefree d)
    (hmod : d % 24 = 23) (hr : legendreSym p (-(d : ℤ)) = sign)
    (hsep : (d + 1) ^ 2 < 24 * p)
    (hclass : 8 * formClassNumber (-(d : ℤ)) < p + 1)
    (J : ℂ → ℂ) (Y : ℝ)
    (hanalytic : AnalyticOnNhd ℂ
      (cmPoleClearedFunction (-(d : ℤ)) J) {w | 0 < w.im})
    (htrans : ∀ (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane),
      cmPoleClearedFunction (-(d : ℤ)) J
        ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ
          (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ 4 *
            cmPoleClearedFunction (-(d : ℤ)) J z)
    (hgerm : ∀ z : UpperHalfPlane,
      (fun w => cmPoleFactor (-(d : ℤ)) w ^ 2 * J w) =ᶠ[𝓝[≠] (z : ℂ)]
        cmPoleClearedFunction (-(d : ℤ)) J)
    (hsum : ∀ z : UpperHalfPlane, Y < z.im →
      HasSum (fun n : ℕ =>
        ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
          Function.Periodic.qParam 1 z ^ n) (J z))
    (hfinite : ∀ c ∈ ({0, 1 / 2, 1 / 3} : Set ℝ),
      (↑c : OnePoint ℝ).IsBoundedAt
        (fun z : UpperHalfPlane =>
          ModularForm.discriminant z ^ (8 * formClassNumber (-(d : ℤ))) *
            cmPoleClearedFunction (-(d : ℤ)) J z)
        ((96 * formClassNumber (-(d : ℤ)) + 4 : ℕ) : ℤ)) :
    ¬∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign → p ∣ spt j := by
  obtain ⟨F, hF⟩ := cmClearedModularForm_of_finite_bounds d hmod hsq J Y
    hanalytic htrans hgerm hsum hfinite
  obtain ⟨YF, heq⟩ := principalCMShimuraLift_cleared_eq_on_high_cusp d hmod
    J Y hanalytic hgerm hsum
  apply CMShimuraClearedObstruction.obstruction_of_highCusp_clearing p hp sign hsign
    d hd hsq hmod hr hsep hclass F (fun z => J z) Y YF hsum
  intro z hz
  rw [hF z, heq z hz]
  simp only [cmPoleFactor_eq, Polynomial.eval_mul]

end SptClassification
