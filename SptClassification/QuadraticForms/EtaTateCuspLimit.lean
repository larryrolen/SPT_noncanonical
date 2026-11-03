/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.TateCuspBranch
public import SptClassification.ModularForms.EtaQuotientExpansion

/-!
# The eta parameter at the width-one cusp

The proved Euler expansion of the actual eta quotient selects the same
`-1/9` branch of the Tate parameter as the trigonometric degeneration.
-/

public section

namespace SptClassification.LevelSixWeierstrass

/-- Cancel the nonzero nome before taking a limit at the pole of the eta quotient. -/
theorem tateParameter_eta_eq_euler (z : ℂ) :
    tateParameter (levelSixEtaQuotient z) =
      -levelSixEulerUnit (Function.Periodic.qParam 1 z) /
        (9 * (levelSixEulerUnit (Function.Periodic.qParam 1 z) +
          8 * Function.Periodic.qParam 1 z)) := by
  have hq : Function.Periodic.qParam 1 z ≠ 0 := by
    unfold Function.Periodic.qParam
    exact Complex.exp_ne_zero _
  rw [tateParameter_eq, levelSixEtaQuotient_eq_unit_div_qParam]
  field_simp

/-- The actual eta quotient determines the width-one Tate cusp along every
approach whose nome tends to zero. -/
theorem tendsto_tateParameter_eta_cusp {α : Type*} {l : Filter α}
    (z : α → ℂ)
    (hz : Filter.Tendsto (fun a => Function.Periodic.qParam 1 (z a)) l (nhds 0)) :
    Filter.Tendsto (fun a => tateParameter (levelSixEtaQuotient (z a)))
      l (nhds (-1 / 9)) := by
  have hu : Filter.Tendsto
      (fun a => levelSixEulerUnit (Function.Periodic.qParam 1 (z a))) l (nhds 1) := by
    simpa only [Function.comp_def, levelSixEulerUnit_zero] using
      continuousAt_levelSixEulerUnit_zero.tendsto.comp hz
  have h := hu.neg.div ((hu.add (hz.const_mul 8)).const_mul 9) (by norm_num)
  simp only [mul_zero, add_zero, mul_one] at h
  simp only [tateParameter_eta_eq_euler]
  convert h using 1 <;> rfl

/-- The actual eta candidate and another Tate parameter family agree near the
cusp if they have equal reciprocal invariants and the latter tends to `-1/9`.
This does not assert the missing Weierstrass cusp limit. -/
theorem eventuallyEq_tateParameter_eta_of_cusp_limit {α : Type*} {l : Filter α}
    (z : α → ℂ) {u : α → ℂ}
    (hz : Filter.Tendsto (fun a => Function.Periodic.qParam 1 (z a)) l (nhds 0))
    (hu : Filter.Tendsto u l (nhds (-1 / 9)))
    (heq : ∀ᶠ a in l, tateReciprocalInvariant (u a) =
      tateReciprocalInvariant (tateParameter (levelSixEtaQuotient (z a)))) :
    u =ᶠ[l] (fun a => tateParameter (levelSixEtaQuotient (z a))) :=
  tateParameter_eventuallyEq_of_cusp_limit hu (tendsto_tateParameter_eta_cusp z hz) heq

end SptClassification.LevelSixWeierstrass
