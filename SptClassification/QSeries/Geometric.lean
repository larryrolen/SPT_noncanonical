/- Assembled by AxiomProver. -/

module

public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Formal geometric series and multiplicity weights

In the coefficientwise topology, the geometric series in `X^m` is the inverse
of `1-X^m` for positive `m`. Its square counts ordered pairs of multiplicities.
-/

public section

namespace SptClassification.QSeries

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- The formal geometric series in `X^m`. -/
noncomputable def geometricSeries (m : ℕ) : PowerSeries ℤ := ∑' r : ℕ, (X ^ m) ^ r

/-- The defining coefficientwise sum of a geometric factor. -/
theorem geometricSeries_eq_tsum (m : ℕ) :
    geometricSeries m = ∑' r : ℕ, ((X : PowerSeries ℤ) ^ m) ^ r := by
  rfl

theorem summable_geometricSeries {m : ℕ} (hm : 0 < m) :
    Summable (fun r : ℕ => ((X : PowerSeries ℤ) ^ m) ^ r) :=
  WithPiTopology.summable_pow_of_constantCoeff_eq_zero (by simp [hm.ne'])

theorem geometricSeries_eq_one_add {m : ℕ} (hm : 0 < m) :
    geometricSeries m = 1 + ∑' r : ℕ, (X : PowerSeries ℤ) ^ (m * (r + 1)) := by
  simpa [geometricSeries, pow_mul] using
    (Summable.sum_add_tsum_nat_add 1 (summable_geometricSeries hm)).symm

theorem geometricSeries_mul_one_sub {m : ℕ} (hm : 0 < m) :
    geometricSeries m * (1 - X ^ m) = 1 :=
  WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp [hm.ne'])

theorem geometricSeries_eq_invOfUnit {m : ℕ} (hm : 0 < m) :
    geometricSeries m = (1 - (X : PowerSeries ℤ) ^ m).invOfUnit 1 := by
  have hconst : constantCoeff (1 - (X : PowerSeries ℤ) ^ m) = (1 : ℤ) := by
    simp [hm.ne']
  calc
    geometricSeries m = geometricSeries m *
        ((1 - (X : PowerSeries ℤ) ^ m) * (1 - (X : PowerSeries ℤ) ^ m).invOfUnit 1) := by
      rw [PowerSeries.mul_invOfUnit _ _ hconst, mul_one]
    _ = _ := by rw [← mul_assoc, geometricSeries_mul_one_sub hm, one_mul]

theorem summable_geometricPairs {m : ℕ} (hm : 0 < m) :
    Summable (fun p : ℕ × ℕ => ((X : PowerSeries ℤ) ^ m) ^ p.1 * (X ^ m) ^ p.2) := by
  apply (WithPiTopology.summable_iff_summable_coeff ℤ).mpr
  intro d
  apply summable_of_ne_finset_zero (s := Finset.range (d + 1) ×ˢ Finset.range (d + 1))
  intro p hp
  have hsum : d < p.1 + p.2 := by
    simp only [Finset.mem_product, Finset.mem_range] at hp
    omega
  have hdegree : d ≠ m * (p.1 + p.2) := by nlinarith
  rw [← pow_add, ← pow_mul, coeff_X_pow]
  exact ite_eq_right hdegree

theorem geometricSeries_sq {m : ℕ} (hm : 0 < m) :
    geometricSeries m ^ 2 = ∑' n : ℕ, ((n + 1 : ℕ) : ℤ) • ((X : PowerSeries ℤ) ^ m) ^ n := by
  rw [pow_two, geometricSeries]
  rw [(summable_geometricSeries hm).tsum_mul_tsum_eq_tsum_sum_range
    (summable_geometricSeries hm) (summable_geometricPairs hm)]
  apply tsum_congr
  intro n
  calc
    ∑ k ∈ Finset.range (n + 1), ((X : PowerSeries ℤ) ^ m) ^ k * (X ^ m) ^ (n - k) =
        ∑ _k ∈ Finset.range (n + 1), ((X : PowerSeries ℤ) ^ m) ^ n := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← pow_add, Nat.add_sub_of_le (by simpa using Finset.mem_range.mp hk)]
    _ = _ := by simp

theorem summable_natCast_geometric {m : ℕ} (hm : 0 < m) :
    Summable (fun n : ℕ => ((n + 1 : ℕ) : ℤ) • ((X : PowerSeries ℤ) ^ m) ^ n) := by
  apply (summable_nat_add_iff 1).mp
  have h : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℤ) + 1) •
      (X : PowerSeries ℤ) ^ (m * (j + 1))) :=
    Nat.Partition.summable_genFun_term' (fun _ c => (c : ℤ) + 1) hm.ne'
  simpa [pow_mul] using h

/-- The series recording the positive multiplicity of a part.
Its defining sum is used by the partition generating-series construction. -/
@[expose] noncomputable def weightedGeometricSeries (m : ℕ) : PowerSeries ℤ :=
  ∑' j : ℕ, ((j + 1 : ℕ) : ℤ) • X ^ (m * (j + 1))

theorem weightedGeometricSeries_eq {m : ℕ} (hm : 0 < m) :
    weightedGeometricSeries m = X ^ m * geometricSeries m ^ 2 := by
  rw [weightedGeometricSeries, geometricSeries_sq hm,
    ← (summable_natCast_geometric hm).tsum_mul_left (X ^ m)]
  apply tsum_congr
  intro j
  rw [mul_smul_comm, ← pow_succ', pow_mul]

end SptClassification.QSeries
