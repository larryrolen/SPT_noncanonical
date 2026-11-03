/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.RestrictedSeries
public import SptClassification.QSeries.PrincipalPartIntegral
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Integral formal expansion of the level-six eta quotient

The Euler factors of `η(nτ)` are indexed by positive multiples of `n`.
The partition generating series for these allowed parts is the formal reciprocal
of their product. This gives the expansion at infinity over `ℤ`; comparison with
the analytic quotient is a separate step. See [rolen2026canonical], Section 4.
-/

public section

namespace SptClassification

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- Partitions whose parts are positive multiples of `n`, with integer weights. -/
noncomputable def etaMultiplePartitionSeries (n : ℕ) : PowerSeries ℤ :=
  Nat.Partition.genFun (fun k _ => if n ∣ k then (1 : ℤ) else 0)

theorem coeff_etaMultiplePartitionSeries (n k : ℕ) :
    (etaMultiplePartitionSeries n).coeff k =
      ∑ p : Nat.Partition k,
        p.parts.toFinsupp.prod (fun j _ => if n ∣ j then (1 : ℤ) else 0) := by
  rw [etaMultiplePartitionSeries, Nat.Partition.coeff_genFun]

/-- The unrestricted partition series is the multiple-part series at scale one. -/
theorem etaMultiplePartitionSeries_one :
    etaMultiplePartitionSeries 1 = QSeries.partitionSeries := by
  apply PowerSeries.ext
  intro n
  rw [QSeries.partitionSeries_coeff]
  rw [coeff_etaMultiplePartitionSeries]
  simp [partitionCount_eq_card]

/-- The partition series is the convergent formal product of the geometric
factors for precisely the allowed positive multiples. -/
theorem hasProd_etaMultiplePartitionSeries (n : ℕ) :
    HasProd (fun i : ℕ => if n ∣ i + 1 then QSeries.geometricSeries (i + 1) else 1)
      (etaMultiplePartitionSeries n) := by
  have hfactor (i : ℕ) :
      QSeries.partitionFactor (fun k _ => if n ∣ k then (1 : ℤ) else 0) i =
        if n ∣ i + 1 then QSeries.geometricSeries (i + 1) else 1 := by
    by_cases hi : n ∣ i + 1
    · rw [ite_eq_left hi, QSeries.geometricSeries_eq_one_add (Nat.succ_pos i)]
      simp [QSeries.partitionFactor, hi]
    · simp [QSeries.partitionFactor, hi]
  convert Nat.Partition.hasProd_genFun (fun k _ => if n ∣ k then (1 : ℤ) else 0) using 1
  · funext i
    exact (hfactor i).symm
  · rfl

/-- The partition series for multiples of `n` is the corresponding infinite
Euler product of formal geometric factors. -/
theorem etaMultiplePartitionSeries_eq_tprod (n : ℕ) :
    etaMultiplePartitionSeries n =
      ∏' i : ℕ, if n ∣ i + 1 then QSeries.geometricSeries (i + 1) else 1 :=
  (hasProd_etaMultiplePartitionSeries n).tprod_eq.symm

/-- The empty partition is the unique contribution to the constant coefficient. -/
theorem etaMultiplePartitionSeries_constantCoeff (n : ℕ) :
    constantCoeff (etaMultiplePartitionSeries n) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [etaMultiplePartitionSeries, Nat.Partition.coeff_genFun]

/-- The integral Euler factor series, formally the product over positive
multiples of `n` of `(1 - q^m)`. -/
noncomputable def etaEulerSeries (n : ℕ) : PowerSeries ℤ :=
  (etaMultiplePartitionSeries n).invOfUnit 1

theorem etaEulerSeries_eq_invOfUnit (n : ℕ) :
    etaEulerSeries n = (etaMultiplePartitionSeries n).invOfUnit 1 := (rfl)

theorem etaEulerSeries_mul_partition (n : ℕ) :
    etaEulerSeries n * etaMultiplePartitionSeries n = 1 := by
  rw [etaEulerSeries, mul_comm]
  exact PowerSeries.mul_invOfUnit _ _ (etaMultiplePartitionSeries_constantCoeff n)

theorem etaEulerSeries_constantCoeff (n : ℕ) :
    constantCoeff (etaEulerSeries n) = 1 := by
  have h := congrArg constantCoeff (etaEulerSeries_mul_partition n)
  simpa [map_mul, etaMultiplePartitionSeries_constantCoeff] using h

/-- Euler factors supported on the positive multiples of `n` converge in the
coefficientwise topology. -/
theorem multipliable_etaEulerFactors (n : ℕ) :
    Multipliable (fun i : ℕ =>
      if n ∣ i + 1 then (1 - (X : PowerSeries ℤ) ^ (i + 1)) else 1) := by
  let f : ℕ → PowerSeries ℤ := fun i =>
    if n ∣ i + 1 then -(X ^ (i + 1)) else 0
  have horder : Filter.Tendsto (fun i => (f i).order)
      Filter.atTop (nhds ⊤) := by
    apply ENat.tendsto_nhds_top_iff_natCast_lt.mpr
    intro d
    refine Filter.eventually_atTop.mpr ⟨d, ?_⟩
    intro i hi
    by_cases hdiv : n ∣ i + 1
    · simp only [f, ite_eq_left hdiv, PowerSeries.order_neg,
        PowerSeries.order_X_pow]
      exact_mod_cast (show d < i + 1 by omega)
    · simp [f, hdiv]
  have h := WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top ℤ horder
  convert h using 1
  funext i
  by_cases hdiv : n ∣ i + 1 <;> simp [f, hdiv, sub_eq_add_neg]

/-- The formal Euler product supported on positive multiples of `n`. -/
noncomputable def etaEulerFactorProduct (n : ℕ) : PowerSeries ℤ :=
  ∏' i : ℕ, if n ∣ i + 1 then (1 - (X : PowerSeries ℤ) ^ (i + 1)) else 1

/-- The formal Euler product is the inverse of the corresponding partition
series; its factors are exactly those in the analytic eta product. -/
theorem etaEulerSeries_eq_factorProduct (n : ℕ) :
    etaEulerSeries n = etaEulerFactorProduct n := by
  let f : ℕ → PowerSeries ℤ := fun i =>
    if n ∣ i + 1 then QSeries.geometricSeries (i + 1) else 1
  let g : ℕ → PowerSeries ℤ := fun i =>
    if n ∣ i + 1 then 1 - X ^ (i + 1) else 1
  have hf : HasProd f (etaMultiplePartitionSeries n) :=
    hasProd_etaMultiplePartitionSeries n
  have hg : HasProd g (etaEulerFactorProduct n) :=
    (multipliable_etaEulerFactors n).hasProd
  have hfg : ∀ i, f i * g i = 1 := by
    intro i
    by_cases hi : n ∣ i + 1
    · simpa [f, g, hi] using QSeries.geometricSeries_mul_one_sub (Nat.succ_pos i)
    · simp [f, g, hi]
  have hmul : etaMultiplePartitionSeries n * etaEulerFactorProduct n = 1 := by
    have h := hf.mul hg
    simp_rw [hfg] at h
    exact h.unique hasProd_one
  have hpart : etaMultiplePartitionSeries n ≠ 0 := by
    intro he
    have h := etaMultiplePartitionSeries_constantCoeff n
    rw [he, map_zero] at h
    norm_num at h
  apply mul_left_cancel₀ hpart
  calc
    etaMultiplePartitionSeries n * etaEulerSeries n = 1 := by
      rw [mul_comm]
      exact etaEulerSeries_mul_partition n
    _ = etaMultiplePartitionSeries n * etaEulerFactorProduct n := hmul.symm

/-- The integral eta series is the limit of its Euler factors. -/
theorem hasProd_etaEulerSeries (n : ℕ) :
    HasProd (fun i : ℕ =>
      if n ∣ i + 1 then (1 - (X : PowerSeries ℤ) ^ (i + 1)) else 1)
      (etaEulerSeries n) := by
  rw [etaEulerSeries_eq_factorProduct]
  exact (multipliable_etaEulerFactors n).hasProd

/-- The formal Euler quotient in `q t(τ) = U(q)`; all coefficients are integers. -/
noncomputable def levelSixFormalEulerUnit : PowerSeries ℤ :=
  etaEulerSeries 1 ^ 5 * etaEulerSeries 3 *
    (etaEulerSeries 2 * etaEulerSeries 6 ^ 5).invOfUnit 1

theorem levelSixFormalEulerUnit_constantCoeff :
    constantCoeff levelSixFormalEulerUnit = 1 := by
  simp [levelSixFormalEulerUnit, etaEulerSeries_constantCoeff,
    PowerSeries.constantCoeff_invOfUnit]

/-- The normalized formal quotient satisfies the same Euler-factor identity as
the analytic expression at the infinity cusp. -/
theorem levelSixFormalEulerUnit_mul_denominator :
    levelSixFormalEulerUnit * (etaEulerSeries 2 * etaEulerSeries 6 ^ 5) =
      etaEulerSeries 1 ^ 5 * etaEulerSeries 3 := by
  have hden : constantCoeff (etaEulerSeries 2 * etaEulerSeries 6 ^ 5) = (1 : ℤ) := by
    simp [etaEulerSeries_constantCoeff]
  unfold levelSixFormalEulerUnit
  rw [mul_assoc, mul_comm ((etaEulerSeries 2 * etaEulerSeries 6 ^ 5).invOfUnit 1),
    PowerSeries.mul_invOfUnit _ _ hden, mul_one]

end SptClassification
