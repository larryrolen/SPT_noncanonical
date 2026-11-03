/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.EtaTateCuspLimit
public import SptClassification.QuadraticForms.ShortTateCuspLimit
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Global identification from the width-one cusp

Analytic continuation turns the local branch selection into equality on the
upper half-plane. The Weierstrass limits and holomorphy remain explicit inputs;
no assertion about the actual marked CM family is admitted here.
-/

public section

namespace SptClassification

open UpperHalfPlane Filter

/-- Two holomorphic families equal near the infinity cusp agree on the upper
half-plane. A high open half-plane contains an ordinary complex neighborhood,
so the usual analytic identity theorem applies. -/
theorem analytic_eqOn_upperHalfPlane_of_eventuallyEq_atImInfty {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f upperHalfPlaneSet)
    (hg : AnalyticOnNhd ℂ g upperHalfPlaneSet)
    (heq : (fun z : UpperHalfPlane => f z) =ᶠ[atImInfty]
      (fun z : UpperHalfPlane => g z)) :
    Set.EqOn f g upperHalfPlaneSet := by
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp heq
  let B : ℝ := max A 0 + 1
  let z₀ : ℂ := ⟨0, B⟩
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right A 0]
  have hAB : A < B := by dsimp [B]; linarith [le_max_left A 0]
  have hn : ∀ᶠ z : ℂ in nhds z₀, max A 0 < z.im := by
    apply (isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    dsimp [z₀, B]
    linarith
  have hfg : f =ᶠ[nhds z₀] g := by
    filter_upwards [hn] with z hz
    exact hA ⟨z, lt_of_le_of_lt (le_max_right A 0) hz⟩
      (le_of_lt (lt_of_le_of_lt (le_max_left A 0) hz))
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_im_gt 0).isPreconnected hB hfg

namespace LevelSixWeierstrass

/-- The coefficient limits, equality of reciprocal invariants and holomorphy
suffice to identify the short-coordinate family with the actual eta parameter.
The hypotheses are independent analytic inputs, not the marked identity itself. -/
theorem shortTateParameter_eq_eta_of_cusp_data
    (a x y : ℂ → ℂ) (k r : ℂ) (hk : k ≠ 0) (hr : r ^ 2 = 3)
    (ha : Tendsto (fun z : UpperHalfPlane => a z) atImInfty (nhds (-k ^ 4 / 3)))
    (hx : Tendsto (fun z : UpperHalfPlane => x z) atImInfty (nhds (11 * k ^ 2 / 3)))
    (hy : Tendsto (fun z : UpperHalfPlane => y z) atImInfty (nhds (-4 * r * k ^ 3)))
    (hu : AnalyticOnNhd ℂ (fun z => shortTateParameter (a z) (x z) (y z))
      upperHalfPlaneSet)
    (hv : AnalyticOnNhd ℂ (fun z => tateParameter (levelSixEtaQuotient z))
      upperHalfPlaneSet)
    (heq : ∀ᶠ z : UpperHalfPlane in atImInfty,
      tateReciprocalInvariant (shortTateParameter (a z) (x z) (y z)) =
        tateReciprocalInvariant (tateParameter (levelSixEtaQuotient z))) :
    ∀ z : UpperHalfPlane,
      shortTateParameter (a z) (x z) (y z) =
        tateParameter (levelSixEtaQuotient z) := by
  have hc := tendsto_shortTateParameter_cusp k r hk hr ha hx hy
  have hq := qParam_tendsto_atImInfty (by norm_num : (0 : ℝ) < 1)
  have hlocal := eventuallyEq_tateParameter_eta_of_cusp_limit
    (fun z : UpperHalfPlane => (z : ℂ)) hq hc heq
  exact fun z => analytic_eqOn_upperHalfPlane_of_eventuallyEq_atImInfty hu hv hlocal z.im_pos

end LevelSixWeierstrass
end SptClassification
