/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.Basic
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun

/-!
# Multiplicity weights for the smallest part

Marking the multiplicity of a specified least allowed part and subtracting the
unmarked count isolates precisely its contribution to the smallest-parts function.

We follow the smallest-part decomposition in [andrews2008].
-/

@[expose] public section

namespace SptClassification

/-- Weight one for allowed parts and zero for smaller parts. -/
def lowerBoundWeight (m i : ℕ) (_c : ℕ) : ℤ := if m ≤ i then 1 else 0

@[simp] theorem lowerBoundWeight_apply (m i c : ℕ) :
    lowerBoundWeight m i c = if m ≤ i then 1 else 0 := by
  rfl

/-- Mark the multiplicity of the least allowed part by adding one. -/
def minimumWeight (m i c : ℕ) : ℤ :=
  if m ≤ i then if i = m then (c : ℤ) + 1 else 1 else 0

@[simp] theorem minimumWeight_apply (m i c : ℕ) :
    minimumWeight m i c =
      (if m ≤ i then if i = m then (c : ℤ) + 1 else 1 else 0) := by
  rfl

/-- The contribution of a specified value to the smallest-part statistic. -/
def minimumContribution {n : ℕ} (m : ℕ) (p : Nat.Partition n) : ℕ :=
  if ∀ i ∈ p.parts, m ≤ i then p.parts.count m else 0

theorem prod_lowerBoundWeight (m : ℕ) (s : Multiset ℕ) :
    s.toFinsupp.prod (lowerBoundWeight m) = if ∀ i ∈ s, m ≤ i then 1 else 0 := by
  simp only [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  by_cases h : ∀ i ∈ s, m ≤ i
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    simp [lowerBoundWeight, h i (Multiset.mem_toFinset.mp hi)]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi, hlt⟩ := h
    apply Finset.prod_eq_zero (Multiset.mem_toFinset.mpr hi)
    simp [lowerBoundWeight, hlt.not_ge]

theorem prod_minimumWeight (m : ℕ) (s : Multiset ℕ) :
    s.toFinsupp.prod (minimumWeight m) =
      if ∀ i ∈ s, m ≤ i then (s.count m : ℤ) + 1 else 0 := by
  simp only [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  by_cases h : ∀ i ∈ s, m ≤ i
  · rw [ite_eq_left h]
    calc
      ∏ i ∈ s.toFinset, minimumWeight m i (s.count i) = minimumWeight m m (s.count m) := by
        apply Finset.prod_eq_single m
        · intro i hi him
          simp [minimumWeight, h i (Multiset.mem_toFinset.mp hi), him]
        · intro hm
          have hm' : m ∉ s := by simpa using hm
          simp [minimumWeight, Multiset.count_eq_zero.mpr hm']
      _ = _ := by simp [minimumWeight]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨i, hi, hlt⟩ := h
    apply Finset.prod_eq_zero (Multiset.mem_toFinset.mpr hi)
    simp [minimumWeight, hlt.not_ge]

theorem minimumWeight_sub_lowerBoundWeight {n : ℕ} (m : ℕ) (p : Nat.Partition n) :
    p.parts.toFinsupp.prod (minimumWeight m) - p.parts.toFinsupp.prod (lowerBoundWeight m) =
      (minimumContribution m p : ℤ) := by
  rw [prod_minimumWeight, prod_lowerBoundWeight]
  unfold minimumContribution
  split_ifs <;> simp

theorem sum_minimumContribution {n : ℕ} (p : Nat.Partition n) :
    ∑ m ∈ Finset.Icc 1 n, minimumContribution m p = smallestMultiplicity p := by
  have h := Multiset.sum_count_eq_card (s := Finset.Icc 1 n)
    (m := p.parts.filter fun a => ∀ b ∈ p.parts, a ≤ b) (by
      intro a ha
      have ha' := (Multiset.mem_filter.mp ha).1
      exact Finset.mem_Icc.mpr ⟨p.parts_pos ha', Nat.Partition.le_of_mem_parts ha'⟩)
  simpa only [Multiset.count_filter, minimumContribution, smallestMultiplicity_eq_countP,
    Multiset.countP_eq_card_filter] using h

theorem minimumContribution_eq_zero_of_lt {n m : ℕ} (p : Nat.Partition n) (hnm : n < m) :
    minimumContribution m p = 0 := by
  have hm : m ∉ p.parts := fun h => (Nat.Partition.le_of_mem_parts h).not_gt hnm
  simp [minimumContribution, Multiset.count_eq_zero.mpr hm]

@[simp] theorem minimumContribution_zero {n : ℕ} (p : Nat.Partition n) :
    minimumContribution 0 p = 0 := by
  have h : 0 ∉ p.parts := fun h => (p.parts_pos h).false
  simp [minimumContribution, Multiset.count_eq_zero.mpr h]

theorem spt_eq_sum_minimumContribution (n : ℕ) :
    spt n = ∑ m ∈ Finset.Icc 1 n, ∑ p : Nat.Partition n, minimumContribution m p := by
  rw [spt_eq_sum_partitions]
  simp only [← sum_minimumContribution]
  rw [Finset.sum_comm]

end SptClassification
