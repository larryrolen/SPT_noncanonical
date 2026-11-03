/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsRationalZeros

/-!
# Elementary bound for complete character correlations

The exceptional terms in a higher character moment can always be bounded
by the number of residues, independently of their multiplicities. This is the
elementary side of the complete-sum estimate; the sharper off-diagonal Weil
bound remains a separate analytic input [trevino2012].
-/

public section

namespace SptClassification

/-- Every finite character sum has norm at most the number of terms. The
statement includes zero character values. -/
theorem norm_character_sum_le_card (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (s : Finset (ZMod p))
    (f : ZMod p → ZMod p) :
    ‖∑ x ∈ s, χ (f x)‖ ≤ (s.card : ℝ) := by
  have hterm (x : ZMod p) : ‖χ (f x)‖ ≤ (1 : ℝ) := by
    by_cases hz : χ (f x) = 0
    · simp [hz]
    · rw [norm_character_value_eq_one p χ (f x) hz]
  calc
    ‖∑ x ∈ s, χ (f x)‖ ≤ ∑ x ∈ s, ‖χ (f x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ s, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hterm x)
    _ = (s.card : ℝ) := by simp

/-- The sum of the norms of character values counts precisely the terms at
which the character is nonzero. -/
theorem sum_norm_character_eq_card_nonzero (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (s : Finset (ZMod p))
    (f : ZMod p → ZMod p) :
    (∑ x ∈ s, ‖χ (f x)‖) =
      ((s.filter (fun x => f x ≠ 0)).card : ℝ) := by
  calc
    (∑ x ∈ s, ‖χ (f x)‖) =
        ∑ x ∈ s, if f x ≠ 0 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x = 0
      · simp [hx, character_apply_eq_zero_iff p χ]
      · have hχ : χ (f x) ≠ 0 :=
          (character_apply_eq_zero_iff p χ (f x)).not.mpr hx
        simp [hx, norm_character_value_eq_one p χ (f x) hχ]
    _ = ((s.filter (fun x => f x ≠ 0)).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp

/-- The triangle bound counts only residues at which the character is
nonzero. In a rational correlation these are precisely the residues away
from its zeros and poles. -/
theorem norm_character_sum_le_card_nonzero (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (s : Finset (ZMod p))
    (f : ZMod p → ZMod p) :
    ‖∑ x ∈ s, χ (f x)‖ ≤
      ((s.filter (fun x => f x ≠ 0)).card : ℝ) := by
  calc
    ‖∑ x ∈ s, χ (f x)‖ ≤ ∑ x ∈ s, ‖χ (f x)‖ := norm_sum_le _ _
    _ = ((s.filter (fun x => f x ≠ 0)).card : ℝ) :=
      sum_norm_character_eq_card_nonzero p χ s f

/-- The elementary complete-correlation bound subtracts every distinct
zero or pole of the rational function from the number of contributing
residues [trevino2012]. -/
theorem norm_complete_character_shift_correlation_le_nonzero (p : ℕ)
    [Fact p.Prime] (χ : DirichletCharacter ℂ p) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (u : ι → ZMod p) (v : κ → ZMod p) :
    ‖∑ x : ZMod p,
      χ ((∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j)))‖ ≤
      ((Finset.univ.filter (fun x : ZMod p =>
        x ∉ (s.image fun i => -u i) ∪ (t.image fun j => -v j))).card : ℝ) := by
  have hfilter :
      (Finset.univ.filter (fun x : ZMod p =>
        (∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j)) ≠ 0)) =
      Finset.univ.filter (fun x : ZMod p =>
        x ∉ (s.image fun i => -u i) ∪ (t.image fun j => -v j)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_congr (shift_product_ratio_zero_iff p s t u v x)
  simpa only [hfilter] using norm_character_sum_le_card_nonzero p χ Finset.univ
    (fun x => (∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j)))

/-- The elementary bound in terms of the exact number of distinct roots in
the numerator and denominator. Repeated factors contribute only one omitted
residue [trevino2012]. -/
theorem norm_complete_character_shift_correlation_le_sub_roots (p : ℕ)
    [Fact p.Prime] (χ : DirichletCharacter ℂ p) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (u : ι → ZMod p) (v : κ → ZMod p) :
    ‖∑ x : ZMod p,
      χ ((∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j)))‖ ≤
      (p : ℝ) - (((s.image fun i => -u i) ∪
        (t.image fun j => -v j)).card : ℝ) := by
  let roots := (s.image fun i => -u i) ∪ (t.image fun j => -v j)
  have hsub : roots ⊆ (Finset.univ : Finset (ZMod p)) := Finset.subset_univ _
  have hroots : roots.card ≤ p := by
    simpa using Finset.card_le_card hsub
  have hcard :
      (Finset.univ.filter (fun x : ZMod p => x ∉ roots)).card =
        p - roots.card := by
    calc
      (Finset.univ.filter (fun x : ZMod p => x ∉ roots)).card =
          (Finset.univ \ roots).card := by congr 1; ext x; simp
      _ = (Finset.univ : Finset (ZMod p)).card - roots.card := by
        simp only [Finset.card_sdiff, Finset.inter_univ]
      _ = p - roots.card := by simp
  have hbound := norm_complete_character_shift_correlation_le_nonzero
    p χ s t u v
  change ‖∑ x : ZMod p,
    χ ((∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j)))‖ ≤
      ((Finset.univ.filter (fun x : ZMod p => x ∉ roots)).card : ℝ) at hbound
  rw [hcard, Nat.cast_sub hroots] at hbound
  exact hbound

/-- Any complete correlation of products of shifted linear factors has norm
at most the prime modulus. The result applies to diagonal and off-diagonal
tuples alike. -/
theorem norm_complete_character_shift_correlation_le (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (u : ι → ZMod p) (v : κ → ZMod p) :
    ‖∑ x : ZMod p,
      χ ((∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j)))‖ ≤ (p : ℝ) := by
  simpa using norm_character_sum_le_card p χ Finset.univ
    (fun x => (∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j)))

end SptClassification
