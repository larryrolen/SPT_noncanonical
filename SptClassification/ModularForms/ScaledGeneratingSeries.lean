/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.TwistedAnalyticFunctions
public import SptClassification.ModularForms.EtaQuotientExpansion
public import SptClassification.QSeries.PartitionEulerProduct
public import SptClassification.QSeries.ConvergentDerivatives

/-!
# The analytic generating functions at integral Fourier indices

The series in [rolenManuscript, §2] have exponents `24n-1`. Here they
are realized by rescaling the convergent partition and smallest-parts series.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Topology Manifold

/-- The smallest-parts generating series converges throughout the unit disc. -/
theorem summable_norm_spt {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n => ‖(spt n : ℂ) * q ^ n‖) := by
  have hp := (QSeries.hasSum_eulerDerivative_of_hasSum
    (fun z hz => QSeries.hasSum_partitionCount_inverseEuler hz) hq).summable.norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hp
  intro n
  simp only [norm_mul, norm_pow, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast spt_le_mul_partitionCount n)
    (pow_nonneg (norm_nonneg _) _)

/-- The ordinary smallest-parts series, before the `24n-1` change of exponents. -/
noncomputable def sptAnalyticCore (q : ℂ) : ℂ := ∑' n, (spt n : ℂ) * q ^ n

theorem hasSum_sptAnalyticCore {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => (spt n : ℂ) * q ^ n) (sptAnalyticCore q) :=
  (summable_norm_spt hq).of_norm.hasSum

/-- Rescale an analytic core to exponents `24n-1`. -/
noncomputable def scaledFourierFunction (f : ℂ → ℂ) (τ : UpperHalfPlane) : ℂ :=
  (Function.Periodic.qParam 1 τ)⁻¹ * f (Function.Periodic.qParam 1 τ ^ 24)

theorem scaledFourierFunction_apply (f : ℂ → ℂ) (τ : UpperHalfPlane) :
    scaledFourierFunction f τ =
      (Function.Periodic.qParam 1 τ)⁻¹ * f (Function.Periodic.qParam 1 τ ^ 24) := (rfl)

/-- The rescaling gives the convergent series at the actual integral exponents. -/
theorem scaledFourierFunction_hasSum (c : ℕ → ℂ) (f : ℂ → ℂ)
    (hc : ∀ q : ℂ, ‖q‖ < 1 → HasSum (fun n => c n * q ^ n) (f q))
    (τ : UpperHalfPlane) :
    HasSum (fun n : ℕ => c n * Function.Periodic.qParam 1 τ ^ (24 * (n : ℤ) - 1))
      (scaledFourierFunction f τ) := by
  let q := Function.Periodic.qParam 1 (τ : ℂ)
  have hq : ‖q‖ < 1 := Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have hpow : ‖q ^ 24‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  change HasSum _ (q⁻¹ * f (q ^ 24))
  convert (hc (q ^ 24) hpow).mul_left q⁻¹ using 1
  ext n
  rw [zpow_sub₀ hq0, zpow_one, mul_comm (24 : ℤ), zpow_mul, zpow_natCast]
  simp only [zpow_natCast, zpow_ofNat, div_eq_mul_inv, ← pow_mul]
  rw [Nat.mul_comm n 24]
  ring

/-- A Fourier row supported at `24n-1` can be summed over all integral indices. -/
theorem hasSum_integral_of_twentyFour (a : ℤ → ℂ) (q L : ℂ)
    (ha : ∀ r, r ∉ Set.range (fun n : ℕ => 24 * (n : ℤ) - 1) → a r = 0)
    (hs : HasSum (fun n : ℕ => a (24 * (n : ℤ) - 1) * q ^ (24 * (n : ℤ) - 1)) L) :
    HasSum (fun r : ℤ => a r * q ^ r) L := by
  have hi : Function.Injective (fun n : ℕ => 24 * (n : ℤ) - 1) := by
    intro n m h
    dsimp only at h
    omega
  exact (hi.hasSum_iff (fun r hr => by rw [ha r hr, zero_mul])).mp hs

/-- The actual partition generating function `η(24τ)⁻¹`. -/
noncomputable def scaledPartitionFunction : UpperHalfPlane → ℂ :=
  scaledFourierFunction (fun q => (etaEulerProduct q)⁻¹)

/-- The analytic smallest-parts generating function in the manuscript. -/
noncomputable def scaledSptFunction : UpperHalfPlane → ℂ :=
  scaledFourierFunction sptAnalyticCore

theorem scaledPartitionFunction_eq : scaledPartitionFunction =
    scaledFourierFunction (fun q => (etaEulerProduct q)⁻¹) := (rfl)

theorem scaledSptFunction_eq : scaledSptFunction =
    scaledFourierFunction sptAnalyticCore := (rfl)

/-- The rescaled Euler product is precisely the inverse of `η(24τ)`. -/
theorem scaledPartitionFunction_eq_eta (τ : UpperHalfPlane) :
    scaledPartitionFunction τ = (ModularForm.eta (24 * (τ : ℂ)))⁻¹ := by
  have hη := eta_nat_mul_eq_euler 24 (τ : ℂ)
  norm_num only [Nat.cast_ofNat] at hη
  rw [hη]
  have he : Function.Periodic.qParam 24 (24 * (τ : ℂ)) =
      Function.Periodic.qParam 1 τ := by
    unfold Function.Periodic.qParam
    congr 1
    push_cast
    ring
  rw [he, mul_inv]
  rfl

/-- The actual partition coefficients are the complete integral-index expansion. -/
theorem scaledPartitionFunction_hasSum (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ => (QSeries.partitionFourier r : ℂ) *
      Function.Periodic.qParam 1 τ ^ r) (scaledPartitionFunction τ) := by
  apply hasSum_integral_of_twentyFour
  · intro r hr
    have hz : QSeries.partitionFourier r = 0 := by
      by_contra h
      obtain ⟨hlo, hmod⟩ := QSeries.partitionFourier_support r h
      apply hr
      exact ⟨((r + 1) / 24).toNat, by dsimp only; omega⟩
    simp [hz]
  · simpa only [QSeries.partitionFourier_at, Int.cast_natCast, scaledPartitionFunction] using
      scaledFourierFunction_hasSum (fun n => (partitionCount n : ℂ)) _
        (fun q hq => QSeries.hasSum_partitionCount_inverseEuler hq) τ

/-- The partition-defined smallest-parts coefficients have their analytic sum. -/
theorem scaledSptFunction_hasSum (τ : UpperHalfPlane) :
    HasSum (fun r : ℤ => (QSeries.sptFourier r : ℂ) *
      Function.Periodic.qParam 1 τ ^ r) (scaledSptFunction τ) := by
  apply hasSum_integral_of_twentyFour
  · intro r hr
    have hz : QSeries.sptFourier r = 0 := by
      change QSeries.shiftedTwentyFour _ r = 0
      unfold QSeries.shiftedTwentyFour
      simp only [show ¬ ∃ n : ℕ, r = 24 * (n : ℤ) - 1 from
        fun h => hr (by simpa only [Set.mem_range, eq_comm] using h), dite_false]
    simp [hz]
  · simpa only [QSeries.sptFourier_at, Int.cast_natCast, scaledSptFunction] using
      scaledFourierFunction_hasSum (fun n => (spt n : ℂ)) sptAnalyticCore
        (fun q hq => hasSum_sptAnalyticCore hq) τ

end SptClassification
