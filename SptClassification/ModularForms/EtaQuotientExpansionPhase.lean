/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansionTaylor
public import SptClassification.ModularForms.EtaQuotientCuspsEulerGerms

/-!
# Phase-rescaled Euler series at the width-three cusps

The local parameter at the cusp one-half has width three. Its eta factors
include `η((z-1)/3)` and `η((2z+1)/3)`, so the Euler products carry cubic
phases. We keep those phases in the formal coefficients and identify the
resulting convergent series with the actual analytic Euler factors. This is
a cusp-expansion prerequisite for the level-six coordinate in
[rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

open PowerSeries

/-- The integral eta core with exponents multiplied by `n` and each base
term twisted by `ω`. Its coefficient at `q^(nk)` is `a_k ω^k`, where `a_k`
is the integral eta-core coefficient. -/
noncomputable def etaEulerCoreAtPhaseScale (n : ℕ) (ω : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun j =>
    if n ∣ j then (QSeries.etaIntegralCore.coeff (j / n) : ℂ) * ω ^ (j / n)
    else 0

theorem coeff_etaEulerCoreAtPhaseScale (n j : ℕ) (ω : ℂ) :
    (etaEulerCoreAtPhaseScale n ω).coeff j =
      if n ∣ j then (QSeries.etaIntegralCore.coeff (j / n) : ℂ) * ω ^ (j / n)
      else 0 := by
  simp [etaEulerCoreAtPhaseScale]

/-- The phase-rescaled Euler series has constant coefficient one. -/
theorem etaEulerCoreAtPhaseScale_constantCoeff (n : ℕ) (ω : ℂ) :
    constantCoeff (etaEulerCoreAtPhaseScale n ω) = 1 := by
  have h : QSeries.etaIntegralCore.coeff 0 = 1 := by
    rw [← etaEulerSeries_one_eq_etaIntegralCore]
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      etaEulerSeries_constantCoeff 1
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [etaEulerCoreAtPhaseScale, h]

/-- For a unit phase, the formal phase-rescaled core sums to the actual
Euler product at `q^n ω` throughout the open unit disc. -/
theorem hasSum_etaEulerCoreAtPhaseScale {n : ℕ} (hn : 0 < n)
    {ω q : ℂ} (hω : ‖ω‖ = 1) (hq : ‖q‖ < 1) :
    HasSum (fun j => (etaEulerCoreAtPhaseScale n ω).coeff j * q ^ j)
      (etaEulerProduct (q ^ n * ω)) := by
  have hi : Function.Injective (fun k : ℕ => n * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hn hab
  have hz : ∀ j, j ∉ Set.range (fun k : ℕ => n * k) →
      (etaEulerCoreAtPhaseScale n ω).coeff j * q ^ j = 0 := by
    intro j hj
    have hndiv : ¬ n ∣ j := by
      rintro ⟨k, rfl⟩
      exact hj ⟨k, rfl⟩
    simp [etaEulerCoreAtPhaseScale, hndiv]
  apply (hi.hasSum_iff hz).mp
  have harg : ‖q ^ n * ω‖ < 1 := by
    rw [norm_mul, norm_pow, hω, mul_one]
    exact pow_lt_one₀ (norm_nonneg q) hq hn.ne'
  have hterm (k : ℕ) :
      (etaEulerCoreAtPhaseScale n ω).coeff (n * k) * q ^ (n * k) =
        (QSeries.etaIntegralCore.coeff k : ℂ) * (q ^ n * ω) ^ k := by
    have hdiv : n * k / n = k := by
      rw [mul_comm n k]
      exact Nat.mul_div_cancel _ hn
    simp [etaEulerCoreAtPhaseScale, hdiv, pow_mul, mul_pow]
    ring
  simpa only [Function.comp_def, hterm] using QSeries.hasSum_etaIntegralCore harg

/-- A trivial phase recovers the ordinary rescaled integral eta core after
base change to complex coefficients. -/
theorem etaEulerCoreAtPhaseScale_one (n : ℕ) :
    etaEulerCoreAtPhaseScale n 1 =
      (etaEulerCoreAtScale n).map (Int.castRingHom ℂ) := by
  apply PowerSeries.ext
  intro j
  by_cases h : n ∣ j <;>
    simp [coeff_etaEulerCoreAtPhaseScale, coeff_etaEulerCoreAtScale,
      PowerSeries.coeff_map, h]

private theorem etaIntegralCore_coeff_one :
    QSeries.etaIntegralCore.coeff 1 = -1 := by
  have h := congrArg (fun F : PowerSeries ℤ => F.coeff 1)
    QSeries.partitionSeries_mul_etaIntegralCore
  norm_num [PowerSeries.coeff_mul, Finset.antidiagonal] at h
  omega

/-- The linear coefficient of the phase-rescaled scale-one Euler factor is
the negative of its phase. -/
theorem etaEulerCoreAtPhaseScale_one_coeff_one (ω : ℂ) :
    (etaEulerCoreAtPhaseScale 1 ω).coeff 1 = -ω := by
  simp [etaEulerCoreAtPhaseScale, etaIntegralCore_coeff_one]

/-- Euler factors supported on powers divisible by `n ≥ 2` have no linear
term, independently of the phase. -/
theorem etaEulerCoreAtPhaseScale_coeff_one_of_two_le
    (n : ℕ) (hn : 2 ≤ n) (ω : ℂ) :
    (etaEulerCoreAtPhaseScale n ω).coeff 1 = 0 := by
  have hndiv : ¬ n ∣ 1 := by
    intro h
    have := Nat.le_of_dvd (by decide : 0 < 1) h
    omega
  simp [etaEulerCoreAtPhaseScale, hndiv]

end SptClassification
