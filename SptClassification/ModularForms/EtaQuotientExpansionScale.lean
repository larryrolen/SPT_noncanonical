/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaQuotientExpansionTaylor

/-!
# Rescaling the integral eta Euler product

The Euler factor of `η(nτ)` obtained from partitions into multiples of `n`
agrees with the rescaled integral eta core. This identifies the two integral
models of the level-six cusp expansion in [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

open PowerSeries
open scoped PowerSeries.WithPiTopology

theorem etaEulerCoreAtScale_eq_subst (n : ℕ) (hn : 0 < n) :
    etaEulerCoreAtScale n =
      PowerSeries.subst ((X : PowerSeries ℤ) ^ n) QSeries.etaIntegralCore := by
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_subst_X_pow hn.ne']
  simp [coeff_etaEulerCoreAtScale]

theorem continuous_etaRescale (n : ℕ) (hn : 0 < n) :
    Continuous (fun f : PowerSeries ℤ =>
      PowerSeries.subst ((X : PowerSeries ℤ) ^ n) f) := by
  rw [continuous_iff_continuousAt]
  intro f
  apply (WithPiTopology.tendsto_iff_coeff_tendsto ℤ _ _ _).2
  intro k
  by_cases hk : n ∣ k
  · simpa [PowerSeries.coeff_subst_X_pow hn.ne', hk] using
      (WithPiTopology.continuous_coeff ℤ (k / n)).tendsto f
  · simp [PowerSeries.coeff_subst_X_pow hn.ne', hk]

private theorem etaEulerFactorProduct_partial_rescale
    (n : ℕ) (hn : 0 < n) (m : ℕ) :
    (∏ i ∈ Finset.range (n * m),
      if n ∣ i + 1 then (1 - (X : PowerSeries ℤ) ^ (i + 1)) else 1) =
      ∏ j ∈ Finset.range m, (1 - (X : PowerSeries ℤ) ^ (n * (j + 1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hblock :
          (∏ j ∈ Finset.range n,
            if n ∣ n * m + j + 1 then
              (1 - (X : PowerSeries ℤ) ^ (n * m + j + 1)) else 1) =
            1 - (X : PowerSeries ℤ) ^ (n * (m + 1)) := by
        rw [Finset.prod_eq_single (n - 1)]
        · have hindex : n * m + (n - 1) + 1 = n * (m + 1) := by
            rw [mul_add, mul_one]
            omega
          simp [hindex]
        · intro j hj hne
          have hnot : ¬ n ∣ n * m + j + 1 := by
            intro hdiv
            have hdiv' : n ∣ j + 1 := by
              have hm : n ∣ n * m := dvd_mul_right n m
              apply (Nat.dvd_add_iff_left hm).2
              convert hdiv using 1; omega
            have hle : n ≤ j + 1 := Nat.le_of_dvd (by omega) hdiv'
            simp only [Finset.mem_range] at hj
            omega
          simp [hnot]
        · intro hne
          have hmem : n - 1 ∈ Finset.range n := by simp; omega
          exact (hne hmem).elim
      rw [mul_add, mul_one, Finset.prod_range_add, ih, hblock,
        Finset.prod_range_succ]

private theorem etaEulerFactorProduct_rescale_step
    (n : ℕ) (hn : 0 < n) (j : ℕ) :
    PowerSeries.subst ((X : PowerSeries ℤ) ^ n)
        (1 - (X : PowerSeries ℤ) ^ (j + 1)) =
      1 - (X : PowerSeries ℤ) ^ (n * (j + 1)) := by
  have hzero : constantCoeff ((X : PowerSeries ℤ) ^ n) = 0 := by
    simp [hn.ne']
  have hsubst : PowerSeries.HasSubst ((X : PowerSeries ℤ) ^ n) :=
    PowerSeries.hasSubst_iff.mpr
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hzero))
  let φ : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ := PowerSeries.substAlgHom hsubst
  have hφ (f : PowerSeries ℤ) : φ f = PowerSeries.subst (X ^ n) f := by
    simp [φ, PowerSeries.substAlgHom, PowerSeries.subst]
  rw [← hφ]
  simp only [map_sub, map_pow, map_one]
  rw [hφ, PowerSeries.subst_X, pow_mul]
  exact hsubst

/-- At every positive scale the partition-based Euler product is the rescaling
of the integral scale-one eta core. -/
theorem etaEulerSeries_eq_coreAtScale (n : ℕ) (hn : 0 < n) :
    etaEulerSeries n = etaEulerCoreAtScale n := by
  have hzero : constantCoeff ((X : PowerSeries ℤ) ^ n) = 0 := by
    simp [hn.ne']
  have hsubst : PowerSeries.HasSubst ((X : PowerSeries ℤ) ^ n) :=
    PowerSeries.hasSubst_iff.mpr
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hzero))
  let φ : PowerSeries ℤ →ₐ[ℤ] PowerSeries ℤ := PowerSeries.substAlgHom hsubst
  have hφ (f : PowerSeries ℤ) : φ f = PowerSeries.subst (X ^ n) f := by
    simp [φ, PowerSeries.substAlgHom, PowerSeries.subst]
  have hfinite (m : ℕ) :
      (∏ j ∈ Finset.range m, (1 - (X : PowerSeries ℤ) ^ (n * (j + 1)))) =
        PowerSeries.subst (X ^ n)
          (∏ j ∈ Finset.range m, (1 - (X : PowerSeries ℤ) ^ (j + 1))) := by
    rw [← hφ, map_prod]
    simp_rw [hφ, etaEulerFactorProduct_rescale_step n hn]
  have hbase : Filter.Tendsto
      (fun m : ℕ => ∏ j ∈ Finset.range m, (1 - (X : PowerSeries ℤ) ^ (j + 1)))
      Filter.atTop (nhds (etaEulerSeries 1)) := by
    simpa using (hasProd_etaEulerSeries 1).tendsto_prod_nat
  have hscaled : Filter.Tendsto
      (fun m : ℕ => ∏ j ∈ Finset.range m,
        (1 - (X : PowerSeries ℤ) ^ (n * (j + 1))))
      Filter.atTop (nhds (etaEulerCoreAtScale n)) := by
    have h := ((continuous_etaRescale n hn).continuousAt.tendsto).comp hbase
    rw [etaEulerSeries_one_eq_etaIntegralCore] at h
    rw [etaEulerCoreAtScale_eq_subst n hn]
    simpa only [Function.comp_def, ← hfinite] using h
  have hindex : Filter.Tendsto (fun m : ℕ => n * m)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    refine Filter.eventually_atTop.2 ⟨b, ?_⟩
    intro m hm
    exact le_trans hm (by simpa using Nat.mul_le_mul_right m hn)
  have hfull : Filter.Tendsto
      (fun m : ℕ => ∏ i ∈ Finset.range m,
        if n ∣ i + 1 then (1 - (X : PowerSeries ℤ) ^ (i + 1)) else 1)
      Filter.atTop (nhds (etaEulerSeries n)) := by
    exact (hasProd_etaEulerSeries n).tendsto_prod_nat
  have hsubseq : Filter.Tendsto
      (fun m : ℕ => ∏ j ∈ Finset.range m,
        (1 - (X : PowerSeries ℤ) ^ (n * (j + 1))))
      Filter.atTop (nhds (etaEulerSeries n)) := by
    convert hfull.comp hindex using 1
    funext m
    exact (etaEulerFactorProduct_partial_rescale n hn m).symm
  exact tendsto_nhds_unique hsubseq hscaled

/-- The partition-based integral quotient and the quotient obtained by rescaling
the eta core are the same formal expansion of `q t(τ)`. -/
theorem levelSixFormalEulerUnit_eq_rescaled :
    levelSixFormalEulerUnit = levelSixRescaledEulerUnit := by
  have hden : etaEulerSeries 2 * etaEulerSeries 6 ^ 5 ≠ 0 := by
    intro h
    have hc := congrArg constantCoeff h
    simpa [etaEulerSeries_constantCoeff] using hc
  apply mul_right_cancel₀ hden
  rw [levelSixFormalEulerUnit_mul_denominator,
    etaEulerSeries_eq_coreAtScale 1 (by decide),
    etaEulerSeries_eq_coreAtScale 2 (by decide),
    etaEulerSeries_eq_coreAtScale 3 (by decide),
    etaEulerSeries_eq_coreAtScale 6 (by decide)]
  exact levelSixRescaledEulerUnit_mul_coreFactors.symm

end SptClassification
