/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMShimuraCuspGerm
public import SptClassification.ModularForms.LevelSixFiniteCuspCharts

/-!
# Finite-cusp germs of the independent principal Shimura lift

The full-input Atkin–Lehner covariance identifies each finite-cusp slash
with a translated copy of the high-infinity Fourier germ. The translation
contributes only a unit-modulus phase to the nome. This is the cusp argument
after equation (J) in [rolenManuscript, Section 4].
-/

public section

namespace SptClassification

/-- The actual principal lift has a holomorphic zero-constant-term germ in
each normalized finite-cusp chart, provided its Borcherds/Li–Zemel Fourier
row and full-input Atkin–Lehner covariance hold. The same witness `F`
occurs in both hypotheses. -/
theorem principalCMShimuraLift_finite_cusp_germ (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : d % 24 = 23)
    (F : ℂ → ℂ) (Y : ℝ)
    (hsum : ∀ z : UpperHalfPlane, Y < z.im →
      HasSum (fun n : ℕ =>
        ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
          Function.Periodic.qParam 1 z ^ n) (F z))
    (hslash : ∀ (c : FiniteLevelSixCusp) (z : UpperHalfPlane),
      c.weightFourSlash F z = (c.atkinSign : ℂ) * F (c.shiftedPoint z))
    (c : FiniteLevelSixCusp) (z₀ : UpperHalfPlane) (hz₀ : Y < z₀.im) :
    ∃ J : ℂ → ℂ,
      AnalyticAt ℂ J 0 ∧ J 0 = 0 ∧
      ∀ z : UpperHalfPlane, Y < z.im →
        ‖Function.Periodic.qParam 1 z‖ < ‖Function.Periodic.qParam 1 z₀‖ →
          J (Function.Periodic.qParam 1 z) = c.weightFourSlash F z := by
  have hD : (-(d : ℤ)) % 24 = 1 := by omega
  obtain ⟨Jinf, _, hJ, _, hJzero, _, hJq⟩ :=
    principalCMShimuraLift_actual_cusp_germ d hD F Y hsum z₀ hz₀
  let Jc : ℂ → ℂ := fun q => (c.atkinSign : ℂ) * Jinf (c.nomePhase * q)
  have hq₀ : 0 < ‖Function.Periodic.qParam 1 z₀‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hJ0 : AnalyticAt ℂ Jinf 0 := hJ 0 (by simpa using hq₀)
  have hlin : AnalyticAt ℂ (fun q : ℂ => c.nomePhase * q) 0 :=
    analyticAt_const.mul analyticAt_id
  have hcomp : AnalyticAt ℂ
      (Jinf ∘ (fun q : ℂ => c.nomePhase * q)) 0 :=
    AnalyticAt.comp (f := fun q : ℂ => c.nomePhase * q)
      (by simpa using hJ0) hlin
  have hJc : AnalyticAt ℂ Jc 0 := by
    change AnalyticAt ℂ (fun q : ℂ => (c.atkinSign : ℂ) *
      Jinf (c.nomePhase * q)) 0
    exact analyticAt_const.mul (by simpa only [Function.comp_def] using hcomp)
  refine ⟨Jc, hJc, by simp [Jc, hJzero], ?_⟩
  intro z hz hq
  have hzshift : Y < (c.shiftedPoint z).im := by
    rwa [c.shiftedPoint_im]
  have hqshift :
      ‖Function.Periodic.qParam 1 (c.shiftedPoint z)‖ <
        ‖Function.Periodic.qParam 1 z₀‖ := by
    rw [c.qParam_shiftedPoint, norm_mul, c.norm_nomePhase, one_mul]
    exact hq
  have hJshift : Jinf (Function.Periodic.qParam 1 (c.shiftedPoint z)) =
      F (c.shiftedPoint z) := (hJq (c.shiftedPoint z) hzshift hqshift).1
  change (c.atkinSign : ℂ) * Jinf (c.nomePhase *
    Function.Periodic.qParam 1 z) = c.weightFourSlash F z
  rw [← c.qParam_shiftedPoint, hJshift]
  exact (hslash c z).symm

end SptClassification
