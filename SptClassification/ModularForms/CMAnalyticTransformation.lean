/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.CMAnalyticPoleClearing
public import SptClassification.ModularForms.EtaQuotientInvariance
import Mathlib.Topology.Perfect

/-!
# Transformation of the analytically cleared CM lift

The removable extension of the squared CM factor times a meromorphic lift
inherits its transformation law. Punctured germs, rather than the totalized
values at poles, supply the comparison.
-/

public section

namespace SptClassification

open Filter
open scoped Topology MatrixGroups

/-- A continuous extension of punctured germs preserves a transformation law
under a homeomorphism with continuous multiplier. -/
theorem transformation_of_punctured_extension {X : Type*} [TopologicalSpace X]
    [PerfectSpace X] (e : X ≃ₜ X) (f F j : X → ℂ)
    (hF : Continuous F) (hj : Continuous j)
    (hgerm : ∀ x, f =ᶠ[𝓝[≠] x] F)
    (htrans : ∀ x, f (e x) = j x * f x) (x : X) :
    F (e x) = j x * F x := by
  have he : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) := by
    rw [Filter.Tendsto, e.map_punctured_nhds_eq]
  have hleft := (hgerm (e x)).comp_tendsto he
  have heq : (fun y => F (e y)) =ᶠ[𝓝[≠] x] (fun y => j y * F y) := by
    filter_upwards [hleft, hgerm x] with y hy hy'
    change f (e y) = F (e y) at hy
    rw [← hy, htrans y, hy']
  exact tendsto_nhds_unique_of_eventuallyEq
    ((hF.comp e.continuous).continuousAt.mono_left nhdsWithin_le_nhds)
    ((hj.mul hF).continuousAt.mono_left nhdsWithin_le_nhds) heq

/-- The actual paired CM polynomial factor has weight zero on Γ₀(6). -/
theorem cmPoleFactor_gamma0 (D : ℤ) [Fact (D < 0)]
    (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane) :
    cmPoleFactor D ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
      cmPoleFactor D z := by
  simp only [cmPoleFactor_eq]
  rw [levelSixEtaQuotient_gamma0]

/-- Restriction to the upper half-plane preserves a punctured complex germ. -/
theorem upperHalfPlane_punctured_germ {f F : ℂ → ℂ} (z : UpperHalfPlane)
    (h : f =ᶠ[𝓝[≠] (z : ℂ)] F) :
    (fun w : UpperHalfPlane => f w) =ᶠ[𝓝[≠] z] (fun w => F w) := by
  apply h.comp_tendsto
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨UpperHalfPlane.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, UpperHalfPlane.coe_inj] using hw

/-- Interior pole removal preserves the original lift's weight. The analytic
and germ hypotheses are supplied by `cmPoleClearedFunction_analytic`. -/
theorem cmPoleClearedFunction_transformation (D : ℤ) [Fact (D < 0)]
    (f : ℂ → ℂ) (k : ℕ)
    (hF : AnalyticOnNhd ℂ (cmPoleClearedFunction D f) {w | 0 < w.im})
    (hgerm : ∀ z : UpperHalfPlane,
      (fun w => cmPoleFactor D w ^ 2 * f w) =ᶠ[𝓝[≠] (z : ℂ)]
        cmPoleClearedFunction D f)
    (htrans : ∀ (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane),
      f ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
        UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ k * f z)
    (g : CongruenceSubgroup.Gamma0 6) (z : UpperHalfPlane) :
    cmPoleClearedFunction D f ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
      UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ k *
        cmPoleClearedFunction D f z := by
  apply transformation_of_punctured_extension
    (Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ
      (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)))
    (fun w : UpperHalfPlane => cmPoleFactor D w ^ 2 * f w)
    (fun w : UpperHalfPlane => cmPoleClearedFunction D f w)
    (fun w => UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) w ^ k)
  · apply continuous_iff_continuousAt.mpr
    intro w
    exact (hF w w.im_pos).continuousAt.comp UpperHalfPlane.continuous_coe.continuousAt
  · dsimp only [UpperHalfPlane.denom]
    fun_prop
  · intro w
    exact upperHalfPlane_punctured_germ w (hgerm w)
  · intro w
    change cmPoleFactor D ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • w : UpperHalfPlane) ^ 2 *
      f ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • w : UpperHalfPlane) = _
    rw [cmPoleFactor_gamma0, htrans]
    ring

end SptClassification
