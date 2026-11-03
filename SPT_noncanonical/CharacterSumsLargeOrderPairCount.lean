/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsLargeOrderExceptional

/-!
# Counting large-order exceptional pairs

Equal shift multiplicities force each coordinate of a second tuple to lie
in the support of the first. This gives an elementary uniform fiber bound
for the diagonal part of a complete character moment [trevino2012].
-/

public section

namespace SptClassification

noncomputable local instance largeOrderPairCountDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- For a fixed `w`-tuple, at most `w^w` tuples have the same multiplicity
at every shift. The bound remains valid when shifts repeat or the permitted
shift set is empty [trevino2012]. -/
theorem card_shift_tuples_of_equal_counts_le_pow {F : Type*}
    [DecidableEq F] (shifts : Finset F) (w : ℕ) (u : Fin w → F) :
    let indices := (Finset.univ : Finset (Fin w))
    let tuples := indices.pi (fun _ => shifts)
    (tuples.filter (fun v : ∀ i ∈ indices, F =>
      ∀ a : F,
        (indices.filter (fun i => u i = a)).card =
          (indices.filter (fun i => v i (Finset.mem_univ i) = a)).card)).card ≤
      w ^ w := by
  classical
  intro indices tuples
  let support := indices.image u
  have hsub :
      (tuples.filter (fun v : ∀ i ∈ indices, F =>
        ∀ a : F,
          (indices.filter (fun i => u i = a)).card =
            (indices.filter (fun i => v i (Finset.mem_univ i) = a)).card)) ⊆
        indices.pi (fun _ => support) := by
    intro v hv
    have hcount := (Finset.mem_filter.mp hv).2
    apply Finset.mem_pi.mpr
    intro i hi
    have hpos : 0 <
        (indices.filter (fun j =>
          v j (Finset.mem_univ j) = v i hi)).card := by
      apply Finset.card_pos.mpr
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
    rw [← hcount (v i hi)] at hpos
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    exact Finset.mem_image.mpr
      ⟨j, (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
  calc
    (tuples.filter (fun v : ∀ i ∈ indices, F =>
      ∀ a : F,
        (indices.filter (fun i => u i = a)).card =
          (indices.filter (fun i => v i (Finset.mem_univ i) = a)).card)).card ≤
        (indices.pi (fun _ => support)).card := Finset.card_le_card hsub
    _ = support.card ^ w := by simp [indices, Finset.card_pi]
    _ ≤ w ^ w := by
      gcongr
      simpa [support, indices] using (Finset.card_image_le :
        (indices.image u).card ≤ indices.card)

/-- The number of pairs of ordered `w`-tuples with matching shift
multiplicities is at most `|shifts|^w · w^w` [trevino2012]. -/
theorem card_equal_count_shift_pairs_le {F : Type*} [DecidableEq F]
    (shifts : Finset F) (w : ℕ) :
    let indices := (Finset.univ : Finset (Fin w))
    let tuples := indices.pi (fun _ => shifts)
    ((tuples.product tuples).filter (fun uv :
        (∀ i ∈ indices, F) × (∀ i ∈ indices, F) =>
      ∀ a : F,
        (indices.filter (fun i => uv.1 i (Finset.mem_univ i) = a)).card =
          (indices.filter (fun i => uv.2 i (Finset.mem_univ i) = a)).card)).card ≤
      shifts.card ^ w * w ^ w := by
  classical
  intro indices tuples
  have hcard :
      ((tuples.product tuples).filter (fun uv :
          (∀ i ∈ indices, F) × (∀ i ∈ indices, F) =>
        ∀ a : F,
          (indices.filter (fun i => uv.1 i (Finset.mem_univ i) = a)).card =
            (indices.filter (fun i => uv.2 i (Finset.mem_univ i) = a)).card)).card =
        ∑ u ∈ tuples,
          (tuples.filter (fun v : ∀ i ∈ indices, F =>
            ∀ a : F,
              (indices.filter (fun i => u i (Finset.mem_univ i) = a)).card =
                (indices.filter (fun i => v i (Finset.mem_univ i) = a)).card)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_product tuples tuples _
  rw [hcard]
  calc
    (∑ u ∈ tuples,
      (tuples.filter (fun v : ∀ i ∈ indices, F =>
        ∀ a : F,
          (indices.filter (fun i => u i (Finset.mem_univ i) = a)).card =
            (indices.filter (fun i => v i (Finset.mem_univ i) = a)).card)).card) ≤
        ∑ _u ∈ tuples, w ^ w := by
      apply Finset.sum_le_sum
      intro u _
      exact card_shift_tuples_of_equal_counts_le_pow shifts w
        (fun i => u i (Finset.mem_univ i))
    _ = shifts.card ^ w * w ^ w := by
      simp [tuples, indices, Finset.card_pi]

/-- If the character order exceeds the tuple length, rational-power
exceptions occupy at most `|shifts|^w · w^w` ordered pairs. This bound uses
only the algebraic diagonal classification [trevino2012]. -/
theorem card_large_order_rational_power_shift_pairs_le {F : Type*}
    [Field F] [DecidableEq F] (shifts : Finset F) (w n : ℕ)
    (hn : w < n) :
    let indices := (Finset.univ : Finset (Fin w))
    let tuples := indices.pi (fun _ => shifts)
    ((tuples.product tuples).filter (fun uv :
        (∀ i ∈ indices, F) × (∀ i ∈ indices, F) =>
      ∃ C D : Polynomial F, C ≠ 0 ∧ D ≠ 0 ∧
        (∏ i : Fin w,
          (Polynomial.X + Polynomial.C (uv.1 i (Finset.mem_univ i)))) * D ^ n =
          (∏ j : Fin w,
            (Polynomial.X + Polynomial.C (uv.2 j (Finset.mem_univ j)))) *
            C ^ n)).card ≤ shifts.card ^ w * w ^ w := by
  classical
  intro indices tuples
  have hsub :
      ((tuples.product tuples).filter (fun uv :
          (∀ i ∈ indices, F) × (∀ i ∈ indices, F) =>
        ∃ C D : Polynomial F, C ≠ 0 ∧ D ≠ 0 ∧
          (∏ i : Fin w,
            (Polynomial.X + Polynomial.C (uv.1 i (Finset.mem_univ i)))) * D ^ n =
            (∏ j : Fin w,
              (Polynomial.X + Polynomial.C (uv.2 j (Finset.mem_univ j)))) *
              C ^ n)) ⊆
        (tuples.product tuples).filter (fun uv :
          (∀ i ∈ indices, F) × (∀ i ∈ indices, F) =>
        ∀ a : F,
          (indices.filter (fun i => uv.1 i (Finset.mem_univ i) = a)).card =
            (indices.filter (fun i => uv.2 i (Finset.mem_univ i) = a)).card) := by
    intro uv huv
    obtain ⟨hpair, C, D, hC, hD, hpower⟩ := Finset.mem_filter.mp huv
    apply Finset.mem_filter.mpr
    refine ⟨hpair, ?_⟩
    exact (character_tuple_rational_power_iff_count_eq_of_large_order
      w n hn
      (fun i => uv.1 i (Finset.mem_univ i))
      (fun i => uv.2 i (Finset.mem_univ i))).mp
        ⟨C, D, hC, hD, hpower⟩
  exact (Finset.card_le_card hsub).trans
    (card_equal_count_shift_pairs_le shifts w)

end SptClassification
