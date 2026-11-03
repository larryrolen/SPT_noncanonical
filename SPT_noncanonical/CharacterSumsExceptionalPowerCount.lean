/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsExceptionalPower
public import SptClassification.Arithmetic.CharacterSumsExceptionalCount

/-!
# Counting rational-power character correlations

A rational perfect-power correlation of two `w`-tuples uses at most `w`
distinct shifts. We count all pairs with this support restriction by choosing
their support first [trevino2012].
-/

public section

namespace SptClassification

/-- Pairs of ordered `w`-tuples using at most `w` shifts are covered by the
families indexed by subsets of the available shifts. A pair can belong to
more than one family, so this is an upper bound [trevino2012]. -/
theorem card_small_support_character_shift_pairs_le {α : Type*}
    [DecidableEq α] (shifts : Finset α) (w : ℕ) :
    let indices := (Finset.univ : Finset (Fin w))
    let tuples := indices.pi (fun _ => shifts)
    ((tuples.product tuples).filter (fun uv =>
      ((indices.image (fun i => uv.1 i (Finset.mem_univ i))) ∪
        (indices.image (fun i => uv.2 i (Finset.mem_univ i)))).card ≤ w)).card ≤
      ∑ t ∈ shifts.powerset.filter (fun t => t.card ≤ w), t.card ^ (2 * w) := by
  classical
  intro indices tuples
  let subsets := shifts.powerset.filter (fun t => t.card ≤ w)
  let family (t : Finset α) :=
    (indices.pi (fun _ => t)).product (indices.pi (fun _ => t))
  have hcover :
      ((tuples.product tuples).filter (fun uv =>
        ((indices.image (fun i => uv.1 i (Finset.mem_univ i))) ∪
          (indices.image (fun i => uv.2 i (Finset.mem_univ i)))).card ≤ w)) ⊆
        subsets.biUnion family := by
    intro uv huv
    have hpair := (Finset.mem_filter.mp huv).1
    have hsmall := (Finset.mem_filter.mp huv).2
    let support :=
      (indices.image (fun i => uv.1 i (Finset.mem_univ i))) ∪
        (indices.image (fun i => uv.2 i (Finset.mem_univ i)))
    have hsub : support ⊆ shifts := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact (Finset.mem_pi.mp (Finset.mem_product.mp hpair).1) i hi
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact (Finset.mem_pi.mp (Finset.mem_product.mp hpair).2) i hi
    have hsupp : support ∈ subsets :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hsmall⟩
    have hfamily : uv ∈ family support := by
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_pi.mpr
        intro i hi
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
      · apply Finset.mem_pi.mpr
        intro i hi
        exact Finset.mem_union.mpr (Or.inr
          (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
    exact Finset.mem_biUnion.mpr ⟨support, hsupp, hfamily⟩
  calc
    ((tuples.product tuples).filter (fun uv =>
      ((indices.image (fun i => uv.1 i (Finset.mem_univ i))) ∪
        (indices.image (fun i => uv.2 i (Finset.mem_univ i)))).card ≤ w)).card ≤
        (subsets.biUnion family).card := Finset.card_le_card hcover
    _ ≤ ∑ t ∈ subsets, (family t).card := Finset.card_biUnion_le
    _ = ∑ t ∈ shifts.powerset.filter (fun t => t.card ≤ w),
          t.card ^ (2 * w) := by
      simp [subsets, family, indices, Finset.card_pi, two_mul, pow_add]

noncomputable local instance exceptionalPowerCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- The nonzero polynomial presentations of rational perfect powers form
only a small-support subfamily of the ordered pairs in an even character
moment. The exponent may be any natural number at least two, as required
when the character order varies [trevino2012]. -/
theorem card_rational_power_character_shift_pairs_le {F : Type*}
    [Field F] [DecidableEq F] (shifts : Finset F) (w : ℕ) :
    let indices := (Finset.univ : Finset (Fin w))
    let tuples := indices.pi (fun _ => shifts)
    ((tuples.product tuples).filter (fun uv :
        (∀ i ∈ indices, F) × (∀ i ∈ indices, F) =>
      ∃ n : ℕ, 2 ≤ n ∧ ∃ C D : Polynomial F,
        C ≠ 0 ∧ D ≠ 0 ∧
        (∏ i ∈ indices, (Polynomial.X +
          Polynomial.C (uv.1 i (Finset.mem_univ i)))) * D ^ n =
        (∏ j ∈ indices, (Polynomial.X +
          Polynomial.C (uv.2 j (Finset.mem_univ j)))) * C ^ n)).card ≤
      ∑ t ∈ shifts.powerset.filter (fun t => t.card ≤ w),
        t.card ^ (2 * w) := by
  classical
  intro indices tuples
  have hsubset :
      ((tuples.product tuples).filter (fun uv :
          (∀ i ∈ indices, F) × (∀ i ∈ indices, F) =>
        ∃ n : ℕ, 2 ≤ n ∧ ∃ C D : Polynomial F,
          C ≠ 0 ∧ D ≠ 0 ∧
          (∏ i ∈ indices, (Polynomial.X +
            Polynomial.C (uv.1 i (Finset.mem_univ i)))) * D ^ n =
          (∏ j ∈ indices, (Polynomial.X +
            Polynomial.C (uv.2 j (Finset.mem_univ j)))) * C ^ n)) ⊆
        (tuples.product tuples).filter (fun uv =>
          ((indices.image (fun i => uv.1 i (Finset.mem_univ i))) ∪
            (indices.image (fun i => uv.2 i (Finset.mem_univ i)))).card ≤ w) := by
    intro uv huv
    obtain ⟨hpair, n, hn, C, D, hC, hD, hpower⟩ := Finset.mem_filter.mp huv
    apply Finset.mem_filter.mpr
    refine ⟨hpair, ?_⟩
    exact card_rational_power_shift_support_le w
      (fun i => uv.1 i (Finset.mem_univ i))
      (fun i => uv.2 i (Finset.mem_univ i))
      n hn C D hC hD hpower
  exact (Finset.card_le_card hsubset).trans
    (card_small_support_character_shift_pairs_le shifts w)

end SptClassification
