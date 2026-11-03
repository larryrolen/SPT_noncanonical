/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsExceptional

/-!
# Counting character tuples with few distinct shifts

An exceptional tuple in a higher character moment has no singleton shift.
Its support therefore has size at most half the tuple length. We bound the
number of such tuples by summing over their possible supports [trevino2012].
-/

public section

namespace SptClassification

/-- Tuples of length `2w` drawn from `shifts` and using at most `w` distinct
shifts are covered by the tuple families indexed by subsets of `shifts` of
cardinality at most `w`. The sum counts a tuple more than once if it lies in
several families. -/
theorem card_small_support_character_shift_tuples_le {α : Type*}
    [DecidableEq α] (shifts : Finset α) (w : ℕ) :
    let indices := (Finset.univ : Finset (Fin (2 * w)))
    let tuples := indices.pi (fun _ => shifts)
    (tuples.filter (fun u =>
      (indices.image (fun i => u i (Finset.mem_univ i))).card ≤ w)).card ≤
      ∑ t ∈ shifts.powerset.filter (fun t => t.card ≤ w), t.card ^ (2 * w) := by
  classical
  intro indices tuples
  let subsets := shifts.powerset.filter (fun t => t.card ≤ w)
  let family (t : Finset α) := indices.pi (fun _ => t)
  have hcover :
      (tuples.filter (fun u =>
        (indices.image (fun i => u i (Finset.mem_univ i))).card ≤ w)) ⊆
        subsets.biUnion family := by
    intro u hu
    have htuple := (Finset.mem_filter.mp hu).1
    have hsmall := (Finset.mem_filter.mp hu).2
    let support := indices.image (fun i => u i (Finset.mem_univ i))
    have hsub : support ⊆ shifts := by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_pi.mp htuple) i hi
    have hsupp : support ∈ subsets := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hsmall⟩
    have hfamily : u ∈ family support := by
      apply Finset.mem_pi.mpr
      intro i hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨support, hsupp, hfamily⟩
  calc
    (tuples.filter (fun u =>
      (indices.image (fun i => u i (Finset.mem_univ i))).card ≤ w)).card ≤
        (subsets.biUnion family).card := Finset.card_le_card hcover
    _ ≤ ∑ t ∈ subsets, (family t).card := Finset.card_biUnion_le
    _ = ∑ t ∈ shifts.powerset.filter (fun t => t.card ≤ w),
          t.card ^ (2 * w) := by
      simp [subsets, family, indices, Finset.card_pi]

/-- A repeated tuple has at most `w` distinct shifts, so the support count
also bounds the exceptional tuples of length `2w` [trevino2012]. -/
theorem card_repeated_character_shift_tuples_le {α : Type*}
    [DecidableEq α] (shifts : Finset α) (w : ℕ) :
    let indices := (Finset.univ : Finset (Fin (2 * w)))
    let tuples := indices.pi (fun _ => shifts)
    (tuples.filter (fun u =>
      ∀ a ∈ indices.image (fun i => u i (Finset.mem_univ i)),
        ∃ ij : Fin (2 * w) × Fin (2 * w),
          ij.1 ≠ ij.2 ∧
          u ij.1 (Finset.mem_univ _) = a ∧
          u ij.2 (Finset.mem_univ _) = a)).card ≤
      ∑ t ∈ shifts.powerset.filter (fun t => t.card ≤ w), t.card ^ (2 * w) := by
  classical
  intro indices tuples
  have hsubset :
      (tuples.filter (fun u =>
        ∀ a ∈ indices.image (fun i => u i (Finset.mem_univ i)),
          ∃ ij : Fin (2 * w) × Fin (2 * w),
            ij.1 ≠ ij.2 ∧
            u ij.1 (Finset.mem_univ _) = a ∧
            u ij.2 (Finset.mem_univ _) = a)) ⊆
        tuples.filter (fun u =>
          (indices.image (fun i => u i (Finset.mem_univ i))).card ≤ w) := by
    intro u hu
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hu).1, ?_⟩
    exact card_tuple_image_le_half_of_repeated w
      (fun i => u i (Finset.mem_univ i)) (Finset.mem_filter.mp hu).2
  exact (Finset.card_le_card hsubset).trans
    (card_small_support_character_shift_tuples_le shifts w)

end SptClassification
