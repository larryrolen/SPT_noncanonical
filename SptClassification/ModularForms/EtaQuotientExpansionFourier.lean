/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansionIntegral
public import SptClassification.QSeries.EtaIntegralCore

/-!
# The integral eta core in the level-six expansion

The Euler factor at scale one in the formal level-six eta quotient is the
same integral eta core used in the principal-part Fourier construction.
Its complex coefficient series therefore sums to the actual analytic Euler
product throughout the unit disc. This is the first coefficient comparison
needed for the integral coordinate in [rolenManuscript], Section 4.
-/

public section

namespace SptClassification

open PowerSeries

/-- The scale-one formal Euler factor is the already identified integral eta core. -/
theorem etaEulerSeries_one_eq_etaIntegralCore :
    etaEulerSeries 1 = QSeries.etaIntegralCore := by
  rw [etaEulerSeries_eq_invOfUnit, QSeries.etaIntegralCore_eq_invOfUnit,
    etaMultiplePartitionSeries_one]

/-- The scale-one integral Euler factor sums to the actual Euler product on
the whole unit disc. -/
theorem hasSum_etaEulerSeries_one {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n => ((etaEulerSeries 1).coeff n : ℂ) * q ^ n)
      (etaEulerProduct q) := by
  simpa only [etaEulerSeries_one_eq_etaIntegralCore] using
    QSeries.hasSum_etaIntegralCore hq

/-- The integral eta core with its exponents multiplied by `n`. Its
coefficients vanish away from multiples of `n`. -/
noncomputable def etaEulerCoreAtScale (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun k => if n ∣ k then QSeries.etaIntegralCore.coeff (k / n) else 0

theorem coeff_etaEulerCoreAtScale (n k : ℕ) :
    (etaEulerCoreAtScale n).coeff k =
      if n ∣ k then QSeries.etaIntegralCore.coeff (k / n) else 0 := by
  simp [etaEulerCoreAtScale]

/-- The constant coefficient is unaffected by rescaling the Euler core. -/
theorem etaEulerCoreAtScale_coeff_zero (n : ℕ) :
    (etaEulerCoreAtScale n).coeff 0 = QSeries.etaIntegralCore.coeff 0 := by
  simp [coeff_etaEulerCoreAtScale]

/-- At scale one the rescaled core is the formal Euler product already
constructed from ordinary partitions. -/
theorem etaEulerCoreAtScale_one :
    etaEulerCoreAtScale 1 = etaEulerSeries 1 := by
  rw [etaEulerSeries_one_eq_etaIntegralCore]
  apply PowerSeries.ext
  intro k
  simp [etaEulerCoreAtScale]

/-- The integral rescaled coefficients sum to the actual Euler factor
`∏_{m≥1}(1-q^{nm})` throughout the unit disc. -/
theorem hasSum_etaEulerCoreAtScale {n : ℕ} (hn : 0 < n)
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun k => ((etaEulerCoreAtScale n).coeff k : ℂ) * q ^ k)
      (etaEulerProduct (q ^ n)) := by
  have hi : Function.Injective (fun k : ℕ => n * k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hn hab
  have hz : ∀ k, k ∉ Set.range (fun j : ℕ => n * j) →
      ((etaEulerCoreAtScale n).coeff k : ℂ) * q ^ k = 0 := by
    intro k hk
    have hndiv : ¬ n ∣ k := by
      rintro ⟨j, rfl⟩
      exact hk ⟨j, rfl⟩
    simp [etaEulerCoreAtScale, hndiv]
  apply (hi.hasSum_iff hz).mp
  have hqn : ‖q ^ n‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq hn.ne'
  have hterm (k : ℕ) :
      ((etaEulerCoreAtScale n).coeff (n * k) : ℂ) * q ^ (n * k) =
        (QSeries.etaIntegralCore.coeff k : ℂ) * (q ^ n) ^ k := by
    have hdiv : n * k / n = k := by
      rw [mul_comm n k]
      exact Nat.mul_div_cancel _ hn
    simp [etaEulerCoreAtScale, hdiv, pow_mul]
  simpa only [Function.comp_def, hterm] using QSeries.hasSum_etaIntegralCore hqn

end SptClassification
