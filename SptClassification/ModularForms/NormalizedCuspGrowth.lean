/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ExponentialCuspGrowth
public import SptClassification.ModularForms.ActualNormalizedRepresentative
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable

/-!
# Cusp growth of the normalized representative

The exact cancellation of the derivative terms reduces the cusp estimate in
[rolenManuscript, §2, (2.5)] to the two actual generating functions.
The remaining factors are controlled by the level-one Eisenstein and
quasimodular transformation laws.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped ModularForm

/-- A finite Fourier filter preserves a global exponential height estimate,
which then controls every integral cusp on a bounded real strip. -/
theorem fourierFilter_hasExponentialGrowthOnStrip
    {N : ℕ} [NeZero N] (c : ZMod N → ℂ) (f : UpperHalfPlane → ℂ)
    {C A : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hf : ∀ τ : UpperHalfPlane,
      ‖f τ‖ ≤ C * Real.exp (A * (τ.im + 1 / τ.im)))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {R : ℝ} (hR : 0 ≤ R) :
    HasExponentialGrowthOnStrip (fun τ => fourierFilter c f (γ • τ)) R := by
  apply HasExponentialGrowthOnStrip.of_height_bound
    (C := (∑ j : ZMod N, ‖fourierFilterKernel c j‖) * C)
    (mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hC) hA _ γ hR
  intro τ
  simpa only [mul_assoc] using norm_fourierFilter_le_of_height_bound c f
    (fun y => C * Real.exp (A * (y + 1 / y))) hf τ

/-- A level-one Eisenstein series has exponential growth in every integral
cusp coordinate, uniformly on bounded real strips. -/
theorem eisenstein_hasExponentialGrowthOnStrip {k : ℕ} (hk : 3 ≤ k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {R : ℝ} (hR : 0 ≤ R) :
    HasExponentialGrowthOnStrip (fun τ => ModularForm.E hk (γ • τ)) R := by
  have hb : HasExponentialGrowthOnStrip (fun τ => ModularForm.E hk τ) R :=
    HasExponentialGrowthOnStrip.of_bounded (ModularFormClass.bdd_at_infty (ModularForm.E hk))
  exact ((HasExponentialGrowthOnStrip.denom γ hR).pow k |>.mul hb).congr
    (fun τ => (eisenstein_map_action hk γ τ).symm)

/-- The quasimodular defect is a fixed constant divided by the slash
denominator, so it introduces no uncontrolled cusp growth. -/
theorem E2_hasExponentialGrowthOnStrip
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {R : ℝ} (hR : 0 ≤ R) :
    HasExponentialGrowthOnStrip (fun τ => EisensteinSeries.E2 (γ • τ)) R := by
  have hb : HasExponentialGrowthOnStrip EisensteinSeries.E2 R :=
    HasExponentialGrowthOnStrip.of_bounded EisensteinSeries.isBoundedAtImInfty_E2
  have hdefect : HasExponentialGrowthOnStrip (EisensteinSeries.D2 γ) R := by
    apply ((HasExponentialGrowthOnStrip.const
      (R := R) (2 * Real.pi * Complex.I * (γ 1 0 : ℂ))).div_denom_pow γ 1).congr
    intro τ
    simp [EisensteinSeries.D2, ModularGroup.denom_apply, UpperHalfPlane.denom]
  have hslash := hb.sub ((HasExponentialGrowthOnStrip.const
    (1 / (2 * riemannZeta 2))).mul hdefect)
  apply (hslash.mul ((HasExponentialGrowthOnStrip.denom γ hR).pow 2)).congr
  intro τ
  have h := congrFun (EisensteinSeries.E2_slash_action γ) τ
  simp only [ModularForm.SL_slash_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  have hd := denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
  change EisensteinSeries.E2 (γ • τ) *
    denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ (-(2 : ℤ)) = _ at h
  rw [zpow_neg, zpow_ofNat] at h
  change EisensteinSeries.E2 (γ • τ) /
    denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ 2 = _ at h
  exact ((div_eq_iff (pow_ne_zero 2 hd)).mp h).symm

/-- The normalized fourth-power slash has exponential growth once the actual
filtered partition and smallest-parts functions do. This is a direct estimate
of the manuscript's representative, without a cusp-meromorphy assumption. -/
theorem sptTwistedAnalyticData_normalizedSlash_growth
    (p Q : ℕ) [Fact Q.Prime] (hp : 5 ≤ p)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) {R : ℝ} (hR : 0 ≤ R)
    (hS : HasExponentialGrowthOnStrip
      (fun τ => fourierFilter (negativeSquareResidueSelector Q) scaledSptFunction (γ • τ)) R)
    (hP : HasExponentialGrowthOnStrip
      (fun τ => fourierFilter (negativeSquareResidueSelector Q) scaledPartitionFunction (γ • τ)) R) :
    HasExponentialGrowthOnStrip
      (fun τ => (sptTwistedAnalyticData Q).normalizedRepresentative p hp (γ • τ) ^ 4 /
        denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ (4 * p + 2)) R := by
  have hlow := eisenstein_hasExponentialGrowthOnStrip (k := p - 1) (by omega) γ hR
  have hhigh := eisenstein_hasExponentialGrowthOnStrip (k := p + 1) (by omega) γ hR
  have hE2 := E2_hasExponentialGrowthOnStrip γ hR
  have hnorm := (hlow.mul hS).add (((hhigh.sub (hlow.mul hE2)).mul hP).div_const 288)
  have heq : HasExponentialGrowthOnStrip
      (fun τ => (sptTwistedAnalyticData Q).normalizedRepresentative p hp (γ • τ)) R :=
    hnorm.congr (fun τ => (sptTwistedAnalyticData_normalizedRepresentative_eq p Q hp (γ • τ)).symm)
  exact (heq.pow 4).div_denom_pow γ (4 * p + 2)

end SptClassification
