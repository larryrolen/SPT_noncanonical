/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixEtaInvariant
public import SptClassification.QuadraticForms.TateCuspIdentity

/-!
# Holomorphy of the eta Tate coordinate

The covering formula excludes the singular parameters at every point of the
upper half-plane. In particular the denominator in the Tate coordinate never
vanishes. This discharges the eta holomorphy input in the cusp argument.
-/

public section

namespace SptClassification

namespace ComplexUniformization

/-- The normalized period pair at an arbitrary upper-half-plane point. -/
noncomputable def upperHalfPlanePeriods (z : UpperHalfPlane) : PeriodPair where
  ω₁ := 1
  ω₂ := z
  indep := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have him : b * (z : ℂ).im = 0 := by
      simpa using congrArg Complex.im hab
    have hb : b = 0 := (mul_eq_zero.mp him).resolve_right (ne_of_gt z.im_pos)
    subst b
    have ha : a = 0 := by simpa using congrArg Complex.re hab
    exact ⟨ha, rfl⟩

theorem upperHalfPlanePeriods_omega_one (z : UpperHalfPlane) :
    (upperHalfPlanePeriods z).ω₁ = 1 := (rfl)

theorem upperHalfPlanePeriods_omega_two (z : UpperHalfPlane) :
    (upperHalfPlanePeriods z).ω₂ = (z : ℂ) := (rfl)

end ComplexUniformization

namespace LevelSixWeierstrass

/-- The finite eta parameter avoids all three singular fibers. -/
theorem eta_discriminant_ne_zero (z : UpperHalfPlane) :
    (curve (levelSixEtaQuotient z)).Δ ≠ 0 := by
  let L := ComplexUniformization.upperHalfPlanePeriods z
  letI := ComplexUniformization.curve_isElliptic L
  exact discriminant_ne_zero_of_j_relation _ (ComplexUniformization.curve L).j
    (by norm_num) (ComplexUniformization.levelSixEta_invariant_relation L z
      (ComplexUniformization.upperHalfPlanePeriods_omega_one z)
      (ComplexUniformization.upperHalfPlanePeriods_omega_two z))

theorem eta_add_eight_ne_zero (z : UpperHalfPlane) :
    levelSixEtaQuotient z + 8 ≠ 0 := by
  intro h
  apply eta_discriminant_ne_zero z
  rw [curve_discriminant, h]
  ring

/-- The actual eta Tate coordinate is holomorphic, using the named unmarked
covering formula only to exclude its possible denominator zero. -/
theorem differentiableAt_tateParameter_eta (z : UpperHalfPlane) :
    DifferentiableAt ℂ (fun w => tateParameter (levelSixEtaQuotient w)) (z : ℂ) := by
  simp only [tateParameter_eq]
  exact (differentiableAt_levelSixEtaQuotient z).neg.div
    (((differentiableAt_levelSixEtaQuotient z).add_const 8).const_mul 9)
    (mul_ne_zero (by norm_num) (eta_add_eight_ne_zero z))

theorem analyticOnNhd_tateParameter_eta :
    AnalyticOnNhd ℂ (fun w => tateParameter (levelSixEtaQuotient w))
      UpperHalfPlane.upperHalfPlaneSet := by
  have hd : DifferentiableOn ℂ (fun w => tateParameter (levelSixEtaQuotient w))
      UpperHalfPlane.upperHalfPlaneSet := fun z hz =>
    (differentiableAt_tateParameter_eta ⟨z, hz⟩).differentiableWithinAt
  intro z hz
  exact hd.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)

end LevelSixWeierstrass
end SptClassification
