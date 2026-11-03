/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.MinimumWeights

/-!
# Partitions with bounded parts

The partitions using only parts at most `N` increase to all partitions, and the
coefficient at `n` stabilizes once `N ≥ n`. Their weighted generating series
records exactly these finite counts. This gives the combinatorial approximation
used in the analytic Euler-product argument [rolenManuscript, §3].
-/

public section

namespace SptClassification

/-- The actual number of partitions of `n` using only parts at most `N`. -/
noncomputable def boundedPartitionCount (N n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n => ∀ i ∈ p.parts, i ≤ N)).card

/-- Increasing the bound on the parts can only increase the count. -/
theorem boundedPartitionCount_mono {M N : ℕ} (hMN : M ≤ N) (n : ℕ) :
    boundedPartitionCount M n ≤ boundedPartitionCount N n := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨_, hp⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => (hp i hi).trans hMN⟩

/-- Every bounded-part partition is an ordinary partition. -/
theorem boundedPartitionCount_le (N n : ℕ) :
    boundedPartitionCount N n ≤ partitionCount n := by
  rw [partitionCount_eq_card]
  unfold boundedPartitionCount
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Every part of a partition of `n` is at most `n`, so the counts stabilize. -/
theorem boundedPartitionCount_eq {N n : ℕ} (hn : n ≤ N) :
    boundedPartitionCount N n = partitionCount n := by
  have hf : Finset.univ.filter (fun p : Nat.Partition n => ∀ i ∈ p.parts, i ≤ N) =
      Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro p _ i hi
    exact (Nat.Partition.le_of_mem_parts hi).trans hn
  simp only [boundedPartitionCount, hf, Finset.card_univ, partitionCount_eq_card]

/-- Weight one for a part below the cutoff, zero for a larger part. -/
@[expose] def upperBoundWeight (N i : ℕ) (_c : ℕ) : ℤ := if i ≤ N then 1 else 0

@[simp] theorem upperBoundWeight_apply (N i c : ℕ) :
    upperBoundWeight N i c = if i ≤ N then 1 else 0 := by
  rfl

/-- Multiplying cutoff weights selects exactly multisets satisfying the bound. -/
theorem prod_upperBoundWeight (N : ℕ) (s : Multiset ℕ) :
    s.toFinsupp.prod (upperBoundWeight N) = if ∀ i ∈ s, i ≤ N then 1 else 0 := by
  simp only [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  by_cases h : ∀ i ∈ s, i ≤ N
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    simp [upperBoundWeight, h i (Multiset.mem_toFinset.mp hi)]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi, hlt⟩ := h
    apply Finset.prod_eq_zero (Multiset.mem_toFinset.mpr hi)
    simp [upperBoundWeight, hlt.not_ge]

/-- The formal generating series for partitions with bounded parts. -/
@[expose] noncomputable def boundedPartitionSeries (N : ℕ) : PowerSeries ℤ :=
  Nat.Partition.genFun (upperBoundWeight N)

/-- The bounded partition series is the generating series for the cutoff weight. -/
theorem boundedPartitionSeries_eq_genFun (N : ℕ) :
    boundedPartitionSeries N = Nat.Partition.genFun (upperBoundWeight N) := by
  rfl

/-- The formal coefficient is the actual bounded-part partition count. -/
theorem coeff_boundedPartitionSeries (N n : ℕ) :
    (boundedPartitionSeries N).coeff n = (boundedPartitionCount N n : ℤ) := by
  classical
  rw [boundedPartitionSeries_eq_genFun, Nat.Partition.coeff_genFun]
  simp only [prod_upperBoundWeight, boundedPartitionCount]
  simp

end SptClassification
