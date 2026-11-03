/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.MinimumWeights
public import SptClassification.QSeries.Geometric

/-!
# The smallest-parts generating function

Decomposing by the least part gives the product formula of [andrews2008]. All
infinite sums and products converge in the coefficientwise topology of formal
power series; the coefficients are the actual partition statistic.

## Main results

* `sptSeries_eq_geometric_product_sum`: the least-part product formula.
-/

public section

namespace SptClassification.QSeries

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- The generating function of the genuine smallest-parts statistic. -/
noncomputable def sptSeries : PowerSeries ℤ := PowerSeries.mk fun n => (spt n : ℤ)

@[simp] theorem coeff_sptSeries (n : ℕ) : sptSeries.coeff n = spt n :=
  PowerSeries.coeff_mk _ _

/-- The weighted series recording contributions with specified least part. -/
noncomputable def minimumSeries (m : ℕ) : PowerSeries ℤ :=
  Nat.Partition.genFun (minimumWeight m) - Nat.Partition.genFun (lowerBoundWeight m)

theorem coeff_minimumSeries (m n : ℕ) :
    (minimumSeries m).coeff n = ∑ p : Nat.Partition n, (minimumContribution m p : ℤ) := by
  rw [minimumSeries, map_sub, Nat.Partition.coeff_genFun, Nat.Partition.coeff_genFun,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  exact minimumWeight_sub_lowerBoundWeight m p

theorem coeff_minimumSeries_eq_zero {m n : ℕ} (h : n < m) :
    (minimumSeries m).coeff n = 0 := by
  simp [coeff_minimumSeries, minimumContribution_eq_zero_of_lt _ h]

@[simp] theorem minimumSeries_zero : minimumSeries 0 = 0 := by
  ext n
  simp [coeff_minimumSeries]

theorem sum_coeff_minimumSeries (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, (minimumSeries m).coeff n = sptSeries.coeff n := by
  simp only [coeff_minimumSeries, coeff_sptSeries, spt_eq_sum_minimumContribution,
    Nat.cast_sum]

theorem hasSum_minimumSeries : HasSum minimumSeries sptSeries := by
  apply (WithPiTopology.hasSum_iff_hasSum_coeff ℤ).mpr
  intro n
  rw [← sum_coeff_minimumSeries n]
  apply hasSum_sum_of_ne_finset_zero
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    simp
  · apply coeff_minimumSeries_eq_zero
    simp only [Finset.mem_Icc] at hm
    omega

theorem sptSeries_eq_tsum_minimumSeries : sptSeries = ∑' m : ℕ, minimumSeries m :=
  hasSum_minimumSeries.tsum_eq.symm

/-- The factor for part `i+1` in a weighted partition product. -/
@[expose] noncomputable def partitionFactor (f : ℕ → ℕ → ℤ) (i : ℕ) : PowerSeries ℤ :=
  1 + ∑' j : ℕ, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))

/-- Prescribe a weight at one part, allow larger parts and forbid smaller ones. -/
def tailWeight (m : ℕ) (w : ℕ → ℤ) (i c : ℕ) : ℤ :=
  if i = m then w c else if m < i then 1 else 0

theorem genFun_tailWeight {m : ℕ} (hm : 0 < m) (w : ℕ → ℤ) :
    Nat.Partition.genFun (tailWeight m w) =
      (1 + ∑' j : ℕ, w (j + 1) • (X : PowerSeries ℤ) ^ (m * (j + 1))) *
        Nat.Partition.genFun (lowerBoundWeight (m + 1)) := by
  let A : PowerSeries ℤ := 1 + ∑' j : ℕ, w (j + 1) • X ^ (m * (j + 1))
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have heq : Function.update (partitionFactor (lowerBoundWeight (m + 1))) (m - 1) A =
      partitionFactor (tailWeight m w) := by
    funext i
    by_cases hi : i = m - 1
    · subst i
      simp [partitionFactor, tailWeight, hm', A]
    · have him : i + 1 ≠ m := by omega
      simp [Function.update_of_ne hi, partitionFactor, tailWeight, him,
        lowerBoundWeight_apply]
  have hb : partitionFactor (lowerBoundWeight (m + 1)) (m - 1) = 1 := by
    simp [partitionFactor, lowerBoundWeight_apply, hm']
  have hbase : HasProd (partitionFactor (lowerBoundWeight (m + 1)))
      (Nat.Partition.genFun (lowerBoundWeight (m + 1))) :=
    Nat.Partition.hasProd_genFun _
  have hmarked : HasProd
      (Function.update (partitionFactor (lowerBoundWeight (m + 1))) (m - 1) A)
      (Nat.Partition.genFun (tailWeight m w)) := by
    rw [heq]
    exact Nat.Partition.hasProd_genFun _
  have h := hbase.update' (m - 1) A hmarked
  rw [hb, mul_one] at h
  exact h.symm.trans (mul_comm _ _)

theorem minimumWeight_eq_tailWeight (m : ℕ) :
    minimumWeight m = tailWeight m (fun c => (c : ℤ) + 1) := by
  funext i c
  rw [minimumWeight_apply]
  unfold tailWeight
  split_ifs <;> simp_all <;> omega

theorem lowerBoundWeight_eq_tailWeight (m : ℕ) :
    lowerBoundWeight m = tailWeight m (fun _ => 1) := by
  funext i c
  rw [lowerBoundWeight_apply]
  unfold tailWeight
  split_ifs <;> simp_all <;> omega

theorem minimumSeries_eq_weightedGeometric_mul_tail {m : ℕ} (hm : 0 < m) :
    minimumSeries m = weightedGeometricSeries m *
      Nat.Partition.genFun (lowerBoundWeight (m + 1)) := by
  rw [minimumSeries, minimumWeight_eq_tailWeight, lowerBoundWeight_eq_tailWeight,
    genFun_tailWeight hm, genFun_tailWeight hm, ← sub_mul]
  congr 1
  rw [add_sub_add_left_eq_sub]
  have h₁ : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℤ) + 1) •
      (X : PowerSeries ℤ) ^ (m * (j + 1))) :=
    Nat.Partition.summable_genFun_term' (fun _ c => (c : ℤ) + 1) hm.ne'
  have h₂ : Summable (fun j : ℕ => (1 : ℤ) • (X : PowerSeries ℤ) ^ (m * (j + 1))) :=
    Nat.Partition.summable_genFun_term' (fun _ _ => (1 : ℤ)) hm.ne'
  rw [← h₁.tsum_sub h₂]
  apply tsum_congr
  intro j
  rw [← sub_smul]
  simp

theorem hasProd_geometric_tail (m : ℕ) :
    HasProd (fun i : ℕ => geometricSeries (i + m + 1))
      (Nat.Partition.genFun (lowerBoundWeight (m + 1))) := by
  have hinj : Function.Injective (fun i : ℕ => i + m) := by
    intro i j h
    exact Nat.add_right_cancel h
  have hout (i : ℕ) (hi : i ∉ Set.range (fun j : ℕ => j + m)) :
      partitionFactor (lowerBoundWeight (m + 1)) i = 1 := by
    have him : i < m := by
      by_contra h
      exact hi ⟨i - m, Nat.sub_add_cancel (by omega)⟩
    simp [partitionFactor, lowerBoundWeight_apply, show ¬m + 1 ≤ i + 1 by omega]
  have hbase : HasProd (partitionFactor (lowerBoundWeight (m + 1)))
      (Nat.Partition.genFun (lowerBoundWeight (m + 1))) :=
    Nat.Partition.hasProd_genFun _
  have h := (hinj.hasProd_iff hout).mpr hbase
  have heq : (partitionFactor (lowerBoundWeight (m + 1)) ∘ (fun i : ℕ => i + m)) =
      (fun i : ℕ => geometricSeries (i + m + 1)) := by
    funext i
    rw [geometricSeries_eq_one_add (Nat.succ_pos (i + m))]
    simp [partitionFactor, lowerBoundWeight_apply, show m + 1 ≤ i + m + 1 by omega]
  rwa [heq] at h

theorem genFun_lowerBound_eq_tprod (m : ℕ) :
    Nat.Partition.genFun (lowerBoundWeight (m + 1)) =
      ∏' i : ℕ, geometricSeries (i + m + 1) :=
  (hasProd_geometric_tail m).tprod_eq.symm

theorem sptSeries_eq_tsum_positive_minimumSeries :
    sptSeries = ∑' m : ℕ, minimumSeries (m + 1) := by
  have h := Summable.sum_add_tsum_nat_add 1 hasSum_minimumSeries.summable
  simpa [← sptSeries_eq_tsum_minimumSeries] using h.symm

/-- The generating function obtained by fixing the smallest part and its multiplicity. -/
theorem sptSeries_eq_geometric_product_sum :
    sptSeries = ∑' m : ℕ, X ^ (m + 1) * geometricSeries (m + 1) ^ 2 *
      ∏' j : ℕ, geometricSeries (j + m + 2) := by
  rw [sptSeries_eq_tsum_positive_minimumSeries]
  apply tsum_congr
  intro m
  rw [minimumSeries_eq_weightedGeometric_mul_tail (Nat.succ_pos m),
    weightedGeometricSeries_eq (Nat.succ_pos m), genFun_lowerBound_eq_tprod (m + 1)]
  simp only [Nat.add_assoc]

end SptClassification.QSeries
