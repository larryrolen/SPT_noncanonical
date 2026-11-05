/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.GeneratingSeries
import Mathlib.Tactic.LinearCombination

/-!
# Restricted partition recurrences and finite certificates

The coefficients of the generating function for parts at least `m` satisfy the
usual include/exclude recurrence. A bounded table satisfying this recurrence and
its terminal row is therefore equal to the actual partition coefficients.

This gives a certificate-checking interface for efficient finite computation,
independent of the small-index multiset enumerator.
-/

@[expose] public section

namespace SptClassification.QSeries

open PowerSeries

/-- The generating function of partitions all of whose parts are at least `m`. -/
noncomputable def restrictedPartitionSeries (m : ℕ) : PowerSeries ℤ :=
  Nat.Partition.genFun (lowerBoundWeight m)

/-- The least-part contribution is the weighted geometric series times the restricted tail. -/
theorem minimumSeries_eq_weightedGeometric_mul_restricted {m : ℕ} (hm : 0 < m) :
    minimumSeries m = weightedGeometricSeries m * restrictedPartitionSeries (m + 1) := by
  rw [restrictedPartitionSeries]
  exact minimumSeries_eq_weightedGeometric_mul_tail hm

@[simp] theorem coeff_restrictedPartitionSeries_zero (m : ℕ) :
    (restrictedPartitionSeries m).coeff 0 = 1 := by
  simp [restrictedPartitionSeries, Nat.Partition.coeff_genFun]

/-- Allowing every positive part recovers the ordinary partition count. -/
theorem coeff_restrictedPartitionSeries_one (n : ℕ) :
    (restrictedPartitionSeries 1).coeff n = (partitionCount n : ℤ) := by
  rw [restrictedPartitionSeries, Nat.Partition.coeff_genFun]
  have h (p : Nat.Partition n) : p.parts.toFinsupp.prod (lowerBoundWeight 1) = 1 := by
    rw [prod_lowerBoundWeight]
    exact ite_eq_left (fun i hi => p.parts_pos hi)
  simp [h, partitionCount_eq_card]

/-- A positive integer below the allowed part size has no restricted partitions. -/
theorem coeff_restrictedPartitionSeries_eq_zero {m n : ℕ} (hn : 0 < n) (hmn : n < m) :
    (restrictedPartitionSeries m).coeff n = 0 := by
  rw [restrictedPartitionSeries, Nat.Partition.coeff_genFun]
  apply Finset.sum_eq_zero
  intro p _
  rw [prod_lowerBoundWeight]
  apply ite_eq_right
  intro hmin
  have hpzero : p.parts = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro a ha
    have hal := Nat.Partition.le_of_mem_parts ha
    have ham := hmin a ha
    omega
  have hsum := p.parts_sum
  simp only [hpzero, Multiset.sum_zero] at hsum
  omega

/-- Removing the factor for part `m` raises the least allowed part. -/
theorem restrictedPartitionSeries_succ {m : ℕ} (hm : 0 < m) :
    restrictedPartitionSeries (m + 1) =
      (1 - (X : PowerSeries ℤ) ^ m) * restrictedPartitionSeries m := by
  unfold restrictedPartitionSeries
  have h := genFun_tailWeight hm (fun _ => 1)
  rw [← lowerBoundWeight_eq_tailWeight] at h
  have h' : Nat.Partition.genFun (lowerBoundWeight m) =
      geometricSeries m * Nat.Partition.genFun (lowerBoundWeight (m + 1)) := by
    simpa only [one_smul, geometricSeries_eq_one_add hm] using h
  rw [h', ← mul_assoc, mul_comm (1 - X ^ m), geometricSeries_mul_one_sub hm, one_mul]

/-- The include/exclude recurrence for actual restricted partition coefficients. -/
theorem coeff_restrictedPartitionSeries_recurrence {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (restrictedPartitionSeries m).coeff n =
      (restrictedPartitionSeries (m + 1)).coeff n +
        if m ≤ n then (restrictedPartitionSeries m).coeff (n - m) else 0 := by
  have h := congrArg (PowerSeries.coeff n) (restrictedPartitionSeries_succ hm)
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul'] at h
  linear_combination -h

/-- Every valid bounded recurrence table computes the genuine restricted coefficients. -/
theorem restrictedPartitionTable_sound (B : ℕ) (T : ℕ → ℕ → ℤ)
    (hboundary : ∀ n : ℕ, n ≤ B → T (B + 1) n = if n = 0 then 1 else 0)
    (hstep : ∀ m : ℕ, 1 ≤ m → m ≤ B → ∀ n : ℕ, n ≤ B →
      T m n = T (m + 1) n + if m ≤ n then T m (n - m) else 0)
    {n m : ℕ} (hn : n ≤ B) (hm : 1 ≤ m) (hmb : m ≤ B + 1) :
    T m n = (restrictedPartitionSeries m).coeff n := by
  have main : ∀ n : ℕ, n ≤ B → ∀ m : ℕ, 1 ≤ m → m ≤ B + 1 →
      T m n = (restrictedPartitionSeries m).coeff n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      intro hn
      have aux : ∀ k : ℕ, k ≤ B →
          T (B + 1 - k) n = (restrictedPartitionSeries (B + 1 - k)).coeff n := by
        intro k
        induction k with
        | zero =>
          intro _
          simp only [Nat.sub_zero]
          rw [hboundary n hn]
          by_cases hn0 : n = 0
          · subst n
            simp
          · rw [ite_eq_right hn0, coeff_restrictedPartitionSeries_eq_zero (by omega) (by omega)]
        | succ k ih =>
          intro hk
          have hj : 1 ≤ B + 1 - (k + 1) := by omega
          have hjB : B + 1 - (k + 1) ≤ B := by omega
          have hnext : B + 1 - (k + 1) + 1 = B + 1 - k := by omega
          rw [hstep _ hj hjB n hn, coeff_restrictedPartitionSeries_recurrence (by omega) n,
            hnext, ih (by omega)]
          split_ifs with hle
          · rw [ihn (n - (B + 1 - (k + 1))) (by omega) (by omega)
              (B + 1 - (k + 1)) hj (by omega)]
          · rfl
      intro m hm hmb
      have hindex : B + 1 - (B + 1 - m) = m := by omega
      simpa only [hindex] using aux (B + 1 - m) (by omega)
  exact main n hn m hm hmb

end SptClassification.QSeries
