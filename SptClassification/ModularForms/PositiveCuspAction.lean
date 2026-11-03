/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Topology.Perfect

/-!
# Positive determinant cusp coordinates

The classical determinant-normalized slash of even weight differs from
Mathlib's slash by a constant. These formulas retain that constant when
transporting boundedness from an explicit cusp coordinate.
-/

public section

namespace SptClassification.PositiveCuspAction

open UpperHalfPlane Matrix OnePoint
open scoped MatrixGroups ModularForm
open Filter
open scoped Topology

/-- The classical slash of weight `2*m` for a positive determinant matrix.
Its determinant factor is `det^m`, whereas Mathlib uses `|det|^(2*m-1)`. -/
noncomputable def evenWeightSlash (m : ℕ) (g : GL (Fin 2) ℝ)
    (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  (g.det.val : ℂ) ^ m * f (g • z) / denom g z ^ (2 * m)

/-- Evaluation formula for the classical slash. -/
theorem evenWeightSlash_apply (m : ℕ) (g : GL (Fin 2) ℝ)
    (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    evenWeightSlash m g f z =
      (g.det.val : ℂ) ^ m * f (g • z) / denom g z ^ (2 * m) := (rfl)

/-- Positive determinant removes the conjugation in Mathlib's slash. -/
theorem slash_apply_of_det_pos (k : ℤ) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    (f ∣[k] g) z =
      f (g • z) * (g.det.val : ℂ) ^ (k - 1) * denom g z ^ (-k) := by
  rw [ModularForm.slash_apply]
  change 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det at hg
  simp [UpperHalfPlane.σ, hg, abs_of_pos hg]

/-- The exact constant relating the two slash normalizations. -/
theorem slash_eq_evenWeightSlash (m : ℕ) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    (f ∣[((2 * m : ℕ) : ℤ)] g) z =
      ((g.det.val : ℂ) ^ (((2 * m : ℕ) : ℤ) - 1) / (g.det.val : ℂ) ^ m) *
        evenWeightSlash m g f z := by
  rw [slash_apply_of_det_pos _ g hg]
  simp only [evenWeightSlash, zpow_neg, zpow_natCast]
  have hd : (g.det.val : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  field_simp

/-- Multiplication by a fixed scalar preserves the high-cusp bound. -/
theorem bounded_const_mul {f : UpperHalfPlane → ℂ}
    (hf : IsBoundedAtImInfty f) (a : ℂ) :
    IsBoundedAtImInfty (fun z => a * f z) := by
  obtain ⟨C, Y, h⟩ := isBoundedAtImInfty_iff.mp hf
  refine isBoundedAtImInfty_iff.mpr ⟨‖a‖ * C, Y, ?_⟩
  intro z hz
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h z hz) (norm_nonneg a)

/-- A bound in a classical even-weight chart gives boundedness at the
image of infinity, with Mathlib's cusp convention. -/
theorem boundedAt_of_evenWeightSlash (m : ℕ) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) (f : UpperHalfPlane → ℂ)
    (hf : IsBoundedAtImInfty (evenWeightSlash m g f)) :
    (g • ∞).IsBoundedAt f ((2 * m : ℕ) : ℤ) := by
  rw [OnePoint.IsBoundedAt.smul_iff, OnePoint.isBoundedAt_infty_iff]
  have heq : (f ∣[((2 * m : ℕ) : ℤ)] g) =
      fun z => ((g.det.val : ℂ) ^ (((2 * m : ℕ) : ℤ) - 1) /
        (g.det.val : ℂ) ^ m) * evenWeightSlash m g f z := by
    funext z
    exact slash_eq_evenWeightSlash m g hg f z
  rw [heq]
  exact bounded_const_mul hf _

/-- A cusp-coordinate formula for a punctured representative also describes
its continuous interior extension. The representative's value at a pole is
irrelevant: both comparisons are equalities of punctured germs. -/
theorem evenWeightSlash_eq_of_punctured_germ (m : ℕ) (g : GL (Fin 2) ℝ)
    (f F H : UpperHalfPlane → ℂ) (z : UpperHalfPlane)
    (hF : ContinuousAt F (g • z)) (hH : ContinuousAt H z)
    (hgerm : f =ᶠ[𝓝[≠] (g • z)] F)
    (hchart : evenWeightSlash m g f =ᶠ[𝓝[≠] z] H) :
    evenWeightSlash m g F z = H z := by
  have he : Tendsto (fun w : UpperHalfPlane => g • w)
      (𝓝[≠] z) (𝓝[≠] (g • z)) := by
    change Tendsto (Homeomorph.smul g) (𝓝[≠] z) (𝓝[≠] (g • z))
    rw [Filter.Tendsto, (Homeomorph.smul g).map_punctured_nhds_eq]
    exact le_rfl
  have hcomp := hgerm.comp_tendsto he
  have heq : evenWeightSlash m g F =ᶠ[𝓝[≠] z] H := by
    filter_upwards [hcomp, hchart] with w hw hc
    change f (g • w) = F (g • w) at hw
    simpa only [evenWeightSlash, hw] using hc
  have hden : ContinuousAt (fun w : UpperHalfPlane => denom g w ^ (2 * m)) z := by
    unfold denom
    fun_prop
  have hcont : ContinuousAt (evenWeightSlash m g F) z := by
    exact (continuousAt_const.mul (hF.comp (Homeomorph.smul g).continuous.continuousAt)).div
      hden (pow_ne_zero _ (denom_ne_zero g z))
  exact tendsto_nhds_unique_of_eventuallyEq
    (hcont.mono_left nhdsWithin_le_nhds) (hH.mono_left nhdsWithin_le_nhds) heq

/-- A uniform cusp bound survives filling removable singularities. Only
punctured equality with the representative is needed; the representative
itself need not be continuous at its totalized pole values. -/
theorem boundedAt_of_punctured_germ (m : ℕ) (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) (f F : UpperHalfPlane → ℂ)
    (hF : Continuous F)
    (hgerm : ∀ z : UpperHalfPlane, f =ᶠ[𝓝[≠] z] F)
    (hf : IsBoundedAtImInfty (evenWeightSlash m g f)) :
    (g • ∞).IsBoundedAt F ((2 * m : ℕ) : ℤ) := by
  apply boundedAt_of_evenWeightSlash m g hg F
  obtain ⟨C, Y, hb⟩ := isBoundedAtImInfty_iff.mp hf
  refine isBoundedAtImInfty_iff.mpr ⟨C, Y + 1, ?_⟩
  intro z hz
  have hzY : Y < z.im := by linarith
  have hnear : ∀ᶠ w : UpperHalfPlane in 𝓝[≠] z, Y ≤ w.im := by
    have h := (show ContinuousAt (fun w : UpperHalfPlane => w.im) z by
      fun_prop).eventually (Ioi_mem_nhds hzY)
    exact (h.filter_mono nhdsWithin_le_nhds).mono (fun _ hw => hw.le)
  have he : Tendsto (fun w : UpperHalfPlane => g • w)
      (𝓝[≠] z) (𝓝[≠] (g • z)) := by
    change Tendsto (Homeomorph.smul g) (𝓝[≠] z) (𝓝[≠] (g • z))
    rw [Filter.Tendsto, (Homeomorph.smul g).map_punctured_nhds_eq]
    exact le_rfl
  have hcomp := (hgerm (g • z)).comp_tendsto he
  have hbound : ∀ᶠ w : UpperHalfPlane in 𝓝[≠] z,
      ‖evenWeightSlash m g F w‖ ≤ C := by
    filter_upwards [hnear, hcomp] with w hw heq
    have h := hb w hw
    change f (g • w) = F (g • w) at heq
    simpa only [evenWeightSlash, heq] using h
  have hden : ContinuousAt (fun w : UpperHalfPlane => denom g w ^ (2 * m)) z := by
    unfold denom
    fun_prop
  have hcont : ContinuousAt (evenWeightSlash m g F) z :=
    (continuousAt_const.mul (hF.continuousAt.comp
      (Homeomorph.smul g).continuous.continuousAt)).div
        hden (pow_ne_zero _ (denom_ne_zero g z))
  exact le_of_tendsto (hcont.norm.mono_left nhdsWithin_le_nhds) hbound

end SptClassification.PositiveCuspAction
