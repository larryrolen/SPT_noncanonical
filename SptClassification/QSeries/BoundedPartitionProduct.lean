/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.BoundedParts
public import SptClassification.QSeries.Geometric

/-!
# Finite Euler products for bounded partitions

Cutting off the allowed parts makes the partition generating product finite.
The coefficient identity retains the actual partition counts, including the
empty partition. This is a prerequisite for the convergent Euler-product
comparison used in [rolenManuscript, §3].
-/

public section

namespace SptClassification.QSeries

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- The generating series for partitions with parts at most `N` is the finite
product of the geometric series for those parts. -/
theorem boundedPartitionSeries_eq_prod (N : ℕ) :
    boundedPartitionSeries N = ∏ i ∈ Finset.range N, geometricSeries (i + 1) := by
  rw [boundedPartitionSeries, Nat.Partition.genFun_eq_tprod]
  rw [tprod_eq_prod (s := Finset.range N) (by
    intro i hi
    have h : ¬ i + 1 ≤ N := by simpa using hi
    simp [upperBoundWeight, h, PowerSeries.smul_eq_C_mul])]
  apply Finset.prod_congr rfl
  intro i hi
  have h : i + 1 ≤ N := Finset.mem_range.mp hi
  simpa [upperBoundWeight, h, PowerSeries.smul_eq_C_mul] using
    (geometricSeries_eq_one_add (m := i + 1) (Nat.succ_pos i)).symm

/-- No positive part is allowed at cutoff zero, leaving the empty partition. -/
theorem boundedPartitionSeries_zero : boundedPartitionSeries 0 = 1 := by
  simp [boundedPartitionSeries_eq_prod]

/-- Increasing the cutoff adjoins the geometric factor for the new part. -/
theorem boundedPartitionSeries_succ (N : ℕ) :
    boundedPartitionSeries (N + 1) = boundedPartitionSeries N * geometricSeries (N + 1) := by
  simp only [boundedPartitionSeries_eq_prod, Finset.prod_range_succ]

end SptClassification.QSeries
