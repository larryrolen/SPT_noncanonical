/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.GenericShimuraLift
public import SptClassification.ModularForms.CMAnalyticTransformation

/-! # The independently lifted principal weight-four CM form -/

public section

namespace SptClassification

open scoped Topology

/-- The literature lift applied to the checked principal input `K_d v`.
Its pole support is expressed in terms of the actual principal Weil
coefficients; the lift is independent of the logarithmic CM quotient.
[rolenManuscript, Section 4, equation (J)] -/
theorem principalCMShimuraLift_exists (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : d % 24 = 23) :
    ∃ F : ℂ → ℂ,
      MeromorphicOn F {w | 0 < w.im} ∧
      (∀ (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane),
        F ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
          UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ
            (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ 4 * F z) ∧
      (∀ (cusp : FiniteLevelSixCusp) (z : UpperHalfPlane),
        cusp.weightFourSlash F z = (cusp.atkinSign : ℂ) * F (cusp.shiftedPoint z)) ∧
      (∀ z : UpperHalfPlane,
        (-2 : WithTop ℤ) ≤ meromorphicOrderAt F (z : ℂ)) ∧
      (∀ z : UpperHalfPlane, meromorphicOrderAt F (z : ℂ) < 0 →
        ∃ (x : Theta.DualCoordinates) (n : ℤ), n < 0 ∧
          Theta.quadratic x.toSpace = (n : ℚ) / 24 ∧
          Theta.principalWeilCoefficient d n x.discriminantClass ≠ 0 ∧
          (6 * (x.c : ℂ)) * (z : ℂ) ^ 2 + (x.r : ℂ) * z + x.a = 0) ∧
      ∃ Y : ℝ, ∀ z : UpperHalfPlane, Y < z.im →
        HasSum (fun n : ℕ =>
          ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
            Function.Periodic.qParam 1 z ^ n) (F z) := by
  obtain ⟨F, hmero, htrans, hatkin, horder, hpoles, ⟨Y, hsum⟩⟩ :=
    borcherds_signature21_weightFour_lift (principalKForm d)
      (QSeries.principalKFourier d) d (principalKForm_hasSum d hd) hd
      ((QSeries.principalFourier_zero_of_mod_ne d 0 0 (by norm_num)).2)
  refine ⟨F, hmero, htrans, ?_, horder, ?_, ⟨Y, ?_⟩⟩
  · intro cusp z
    rw [cusp.weightFourSlash_eq_atkinLehner_shift]
    exact hatkin cusp (cusp.shiftedPoint z)
  · intro z hz
    obtain ⟨x, n, hn, hnorm, hc, hquad⟩ := hpoles z hz
    have hc' : Theta.principalWeilCoefficient d n x.discriminantClass ≠ 0 := by
      have hnEq : n = -(d : ℤ) := by
        by_contra hne
        rw [QSeries.principalKFourier_negative d hd n hn, if_neg hne,
          zero_mul] at hc
        exact hc rfl
      simpa only [Theta.principalWeilCoefficient_negative d hd n hn,
        QSeries.principalKFourier_negative d hd n hn, if_pos hnEq,
        one_mul] using hc
    exact ⟨x, n, hn, hnorm, hc', hquad⟩
  · intro z hz
    simpa only [signature21ShimuraRow_eq,
      integralPrincipalShimuraLambertSeries_coeff] using hsum z hz

/-- The actual negative-coefficient support clears every interior pole of
the independently constructed complex lift. -/
theorem principalCMShimuraLift_cleared (d : ℕ)
    [Fact (-(d : ℤ) < 0)] (hd : d % 24 = 23) (hsq : Squarefree d) :
    ∃ F : ℂ → ℂ,
      AnalyticOnNhd ℂ (cmPoleClearedFunction (-(d : ℤ)) F) {w | 0 < w.im} ∧
      (∀ (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane),
        cmPoleClearedFunction (-(d : ℤ)) F
          ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
          UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ
            (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ 4 *
            cmPoleClearedFunction (-(d : ℤ)) F z) ∧
      (∀ (cusp : FiniteLevelSixCusp) (z : UpperHalfPlane),
        cusp.weightFourSlash F z = (cusp.atkinSign : ℂ) * F (cusp.shiftedPoint z)) ∧
      (∀ z : UpperHalfPlane,
        (fun w => cmPoleFactor (-(d : ℤ)) w ^ 2 * F w) =ᶠ[𝓝[≠] (z : ℂ)]
          cmPoleClearedFunction (-(d : ℤ)) F) ∧
      ∃ Y : ℝ, ∀ z : UpperHalfPlane, Y < z.im →
        HasSum (fun n : ℕ =>
          ((integralPrincipalShimuraLambertSeries d).coeff n : ℂ) *
            Function.Periodic.qParam 1 z ^ n) (F z) := by
  obtain ⟨F, hmero, htrans, hatkin, horder, hpoles, hq⟩ :=
    principalCMShimuraLift_exists d hd
  obtain ⟨hanalytic, hgerm⟩ :=
    cmPoleClearedFunction_analytic_of_principalWeil_support hsq hd F hmero horder hpoles
  refine ⟨F, hanalytic, ?_, hatkin, hgerm, hq⟩
  intro g z
  exact cmPoleClearedFunction_transformation _ F 4 hanalytic hgerm htrans g z

end SptClassification
