/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.Basic
public import Mathlib.Data.Finset.Union
import Mathlib.Tactic.NormNum

/-!
# Exact evaluation at small indices

The finite multiset enumerator is proved to enumerate precisely the parts of the
actual partitions of `n`. Summing the least-part statistic over it therefore
computes `spt n`, without replacing the combinatorial definition.

The enumerator is intended for small indices, including the witnesses excluding
congruences modulo two and three.
-/

public section

namespace SptClassification

/-- Enumerate the positive multisets with prescribed sum. -/
def partitionMultisets : ℕ → Finset (Multiset ℕ)
  | 0 => {0}
  | n + 1 => (Finset.range (n + 1)).biUnion fun i =>
      (partitionMultisets (n - i)).image fun s => (i + 1) ::ₘ s
termination_by n => n
decreasing_by omega

/-- The finite enumerator has exactly the parts multisets of natural partitions. -/
theorem mem_partitionMultisets (n : ℕ) (s : Multiset ℕ) :
    s ∈ partitionMultisets n ↔ (∀ a ∈ s, 0 < a) ∧ s.sum = n := by
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
    cases n with
    | zero =>
      constructor
      · intro h
        have hs : s = 0 := by simpa [partitionMultisets] using h
        subst s
        simp
      · rintro ⟨hpos, hsum⟩
        have hs : s = 0 := by
          induction s using Multiset.induction_on with
          | empty => rfl
          | @cons a t _ =>
            have ha := hpos a (by simp)
            simp only [Multiset.sum_cons] at hsum
            omega
        simp [partitionMultisets, hs]
    | succ n =>
      simp only [partitionMultisets, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨i, hi, t, ht, rfl⟩
        obtain ⟨hpos, hsum⟩ := (ih (n - i) (by omega) t).mp ht
        constructor
        · intro a ha
          simp only [Multiset.mem_cons] at ha
          rcases ha with rfl | ha
          · omega
          · exact hpos a ha
        · have hilt : i < n + 1 := Finset.mem_range.mp hi
          have hile : i ≤ n := by omega
          simp only [Multiset.sum_cons]
          omega
      · rintro ⟨hpos, hsum⟩
        induction s using Multiset.induction_on with
        | empty => simp at hsum
        | @cons a t _ =>
          have ha : 0 < a := hpos a (by simp)
          have hsum' : a + t.sum = n + 1 := by simpa using hsum
          refine ⟨a - 1, Finset.mem_range.mpr (by omega), t, ?_, ?_⟩
          · apply (ih (n - (a - 1)) (by omega) t).mpr
            refine ⟨fun b hb => hpos b (by simp [hb]), ?_⟩
            omega
          · congr 1
            omega

/-- A finite evaluator for the smallest-parts statistic. -/
def sptEval (n : ℕ) : ℕ :=
  ∑ s ∈ partitionMultisets n, s.countP fun a => ∀ b ∈ s, a ≤ b

/-- Evaluation is equal to the genuine partition-based definition. -/
theorem spt_eq_sptEval (n : ℕ) : spt n = sptEval n := by
  classical
  rw [spt_eq_sum_partitions]
  unfold sptEval
  apply Finset.sum_bij (fun p _ => p.parts)
  · intro p _
    exact (mem_partitionMultisets n p.parts).mpr ⟨fun _ h => p.parts_pos h, p.parts_sum⟩
  · intro p _ q _ hpq
    exact Nat.Partition.ext hpq
  · intro s hs
    obtain ⟨hpos, hsum⟩ := (mem_partitionMultisets n s).mp hs
    refine ⟨⟨s, fun h => hpos _ h, hsum⟩, Finset.mem_univ _, rfl⟩
  · intro p _
    exact smallestMultiplicity_eq_countP p

@[simp] theorem spt_two : spt 2 = 3 := by
  rw [spt_eq_sptEval]
  decide +kernel

@[simp] theorem spt_three : spt 3 = 5 := by
  rw [spt_eq_sptEval]
  decide +kernel

@[simp] theorem spt_five : spt 5 = 14 := by
  rw [spt_eq_sptEval]
  decide +kernel

/-- The three exact smallest-parts values used to exclude the small prime
moduli in the proof of [rolenManuscript, Corollary 1]. -/
theorem spt_small_prime_values :
    spt 2 = 3 ∧ spt 3 = 5 ∧ spt 5 = 14 :=
  ⟨spt_two, spt_three, spt_five⟩

@[simp] theorem spt_four : spt 4 = 10 := by
  rw [spt_eq_sptEval]
  decide +kernel

@[simp] theorem spt_six : spt 6 = 26 := by
  rw [spt_eq_sptEval]
  decide +kernel

@[simp] theorem spt_seven : spt 7 = 35 := by
  rw [spt_eq_sptEval]
  decide +kernel

@[simp] theorem spt_eight : spt 8 = 57 := by
  rw [spt_eq_sptEval]
  decide +kernel

/-- No arithmetic progression gives a smallest-parts congruence modulo two. -/
theorem no_congruence_mod_two {b : ℕ} (hb : b < 2) :
    ¬∀ n : ℕ, 2 ∣ spt (2 * n + b) := by
  intro h
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · have hbad := h 1
    norm_num at hbad
  · have hbad := h 0
    norm_num at hbad

/-- No arithmetic progression gives a smallest-parts congruence modulo three. -/
theorem no_congruence_mod_three {b : ℕ} (hb : b < 3) :
    ¬∀ n : ℕ, 3 ∣ spt (3 * n + b) := by
  intro h
  rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with rfl | rfl | rfl
  · have hbad := h 1
    norm_num at hbad
  · have hbad := h 0
    norm_num at hbad
  · have hbad := h 1
    norm_num at hbad

end SptClassification
