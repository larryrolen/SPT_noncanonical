/- Assembled by AxiomProver. -/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Multiset.Count

/-!
# The smallest-parts function

The smallest-parts statistic counts each occurrence of a least part in a partition.
The empty partition contributes zero.

## Main definitions

* `smallestMultiplicity`: the contribution of a partition.
* `spt`: Andrews' smallest-parts function.
* `partitionCount`: the ordinary partition function.

## References

We follow [andrews2008].
-/

public section

namespace SptClassification

/-- The number of occurrences of a least part in a partition. -/
def smallestMultiplicity {n : ℕ} (p : Nat.Partition n) : ℕ :=
  p.parts.countP fun a => ∀ b ∈ p.parts, a ≤ b

/-- Andrews' smallest-parts function. -/
noncomputable def spt (n : ℕ) : ℕ :=
  ∑ p : Nat.Partition n, smallestMultiplicity p

/-- The defining sum for the smallest-parts statistic. -/
theorem spt_eq_sum_partitions (n : ℕ) :
    spt n = ∑ p : Nat.Partition n, smallestMultiplicity p := by
  rfl

/-- The least-part multiplicity as a count on the parts multiset. -/
theorem smallestMultiplicity_eq_countP {n : ℕ} (p : Nat.Partition n) :
    smallestMultiplicity p = p.parts.countP (fun a => ∀ b ∈ p.parts, a ≤ b) := by
  rfl

/-- The ordinary partition function. -/
noncomputable def partitionCount (n : ℕ) : ℕ :=
  Fintype.card (Nat.Partition n)

/-- The ordinary partition count is the cardinality of the partition type. -/
theorem partitionCount_eq_card (n : ℕ) :
    partitionCount n = Fintype.card (Nat.Partition n) := by
  rfl

@[simp] theorem smallestMultiplicity_zero (p : Nat.Partition 0) :
    smallestMultiplicity p = 0 := by
  simp [smallestMultiplicity]

@[simp] theorem smallestMultiplicity_one (p : Nat.Partition 1) :
    smallestMultiplicity p = 1 := by
  simp only [smallestMultiplicity, Nat.Partition.partition_one_parts]
  decide

theorem smallestMultiplicity_le_card {n : ℕ} (p : Nat.Partition n) :
    smallestMultiplicity p ≤ p.parts.card :=
  Multiset.countP_le_card _ _

/-- A partition contributes at most the integer being partitioned. -/
theorem smallestMultiplicity_le {n : ℕ} (p : Nat.Partition n) :
    smallestMultiplicity p ≤ n := by
  have card_le_sum (s : Multiset ℕ) (hs : ∀ a ∈ s, 0 < a) : s.card ≤ s.sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      have ha := hs a (by simp)
      have ht := ih (fun b hb => hs b (by simp [hb]))
      simp only [Multiset.card_cons, Multiset.sum_cons]
      omega
  exact (smallestMultiplicity_le_card p).trans
    ((card_le_sum p.parts (fun _ h => p.parts_pos h)).trans_eq p.parts_sum)

/-- A bound used for convergence of the smallest-parts generating function. -/
theorem spt_le_mul_partitionCount (n : ℕ) : spt n ≤ n * partitionCount n := by
  calc
    spt n ≤ ∑ _p : Nat.Partition n, n :=
      Finset.sum_le_sum fun p _ => smallestMultiplicity_le p
    _ = n * partitionCount n := by simp [partitionCount, mul_comm]

@[simp] theorem spt_zero : spt 0 = 0 := by
  simp [spt]

@[simp] theorem spt_one : spt 1 = 1 := by
  simp [spt]

@[simp] theorem partitionCount_zero : partitionCount 0 = 1 := by
  simp [partitionCount]

@[simp] theorem partitionCount_one : partitionCount 1 = 1 := by
  simp [partitionCount]

end SptClassification
