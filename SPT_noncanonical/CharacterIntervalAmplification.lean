/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsDiagonal

/-!
# Character sums on overlapping constant intervals

Every short window inside an interval on which a character is constant has
the same exact character sum. These windows provide the lower side of the
high-moment comparison in Treviño's argument [trevino2012, trevino2017].
-/

public section

namespace SptClassification

/-- Every window contained in a constant interval has the expected short
character sum, with no assumption that its starting integer is positive. -/
theorem sum_constant_character_subinterval (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (start : ℤ) (length : ℕ) (c : ℂ)
    (hconstant : ∀ i : ℕ, i < length →
      χ ((start : ZMod p) + (i : ZMod p)) = c)
    (offset window : ℕ) (hwindow : offset + window ≤ length) :
    (∑ a ∈ intervalResidues p window,
      χ ((start : ZMod p) + (offset : ZMod p) + a)) =
      (window : ℂ) * c := by
  have hlength : length ≤ p :=
    (constant_character_interval_lt_modulus p χ start length c hconstant).le
  have hwle : window ≤ p := by omega
  rw [sum_character_intervalResidues_eq_range p χ
    ((start : ZMod p) + (offset : ZMod p)) window hwle]
  calc
    (∑ i ∈ Finset.range window,
      χ ((start : ZMod p) + (offset : ZMod p) + (i : ZMod p))) =
        ∑ _i ∈ Finset.range window, c := by
      apply Finset.sum_congr rfl
      intro i hi
      have hidx : offset + i < length := by
        have hi' : i < window := Finset.mem_range.mp hi
        omega
      simpa only [Nat.cast_add, add_assoc] using hconstant (offset + i) hidx
    _ = (window : ℂ) * c := by simp

/-- If the common character value is nonzero, every contained short window
has norm exactly its length. -/
theorem norm_sum_constant_character_subinterval (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (start : ℤ) (length : ℕ) (c : ℂ)
    (h2 : 2 ≤ length)
    (hconstant : ∀ i : ℕ, i < length →
      χ ((start : ZMod p) + (i : ZMod p)) = c)
    (offset window : ℕ) (hwindow : offset + window ≤ length) :
    ‖∑ a ∈ intervalResidues p window,
      χ ((start : ZMod p) + (offset : ZMod p) + a)‖ = window := by
  have hc : c ≠ 0 :=
    constant_character_value_ne_zero p χ start length c h2 hconstant
  have hnorm : ‖c‖ = 1 := by
    have hvalue := hconstant 0 (lt_of_lt_of_le (by decide : 0 < 2) h2)
    simp only [Nat.cast_zero, add_zero] at hvalue
    rw [← hvalue]
    exact norm_character_value_eq_one p χ _ (by rw [hvalue]; exact hc)
  rw [sum_constant_character_subinterval p χ start length c hconstant
    offset window hwindow, norm_mul, hnorm]
  simp

/-- The complete even moment counts every short window contained in a
constant interval. There are `length - window + 1` distinct starts, since the
constant interval is shorter than the prime modulus [trevino2012]. -/
theorem constant_character_interval_even_moment_lower (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (start : ℤ) (length : ℕ) (c : ℂ)
    (h2 : 2 ≤ length)
    (hconstant : ∀ i : ℕ, i < length →
      χ ((start : ZMod p) + (i : ZMod p)) = c)
    (window : ℕ) (hwindow : window ≤ length) (w : ℕ) :
    ((length - window + 1 : ℕ) : ℝ) * (window : ℝ) ^ (2 * w) ≤
      ∑ x : ZMod p,
        ‖∑ a ∈ intervalResidues p window, χ (x + a)‖ ^ (2 * w) := by
  let count := length - window + 1
  let f : ZMod p → ℝ := fun x =>
    ‖∑ a ∈ intervalResidues p window, χ (x + a)‖ ^ (2 * w)
  let shift : ℕ → ZMod p := fun i => (start : ZMod p) + (i : ZMod p)
  have hlength : length < p :=
    constant_character_interval_lt_modulus p χ start length c hconstant
  have hcount : count ≤ p := by dsimp [count]; omega
  have hinj : Set.InjOn shift (Finset.range count) := by
    intro i hi j hj hij
    apply intervalResidues_natCast_injOn p count hcount hi hj
    exact add_left_cancel hij
  have hterm (i : ℕ) (hi : i ∈ Finset.range count) :
      f (shift i) = (window : ℝ) ^ (2 * w) := by
    have hiwindow : i + window ≤ length := by
      have hi' : i < count := Finset.mem_range.mp hi
      dsimp [count] at hi'
      omega
    dsimp [f, shift]
    rw [norm_sum_constant_character_subinterval p χ start length c h2
      hconstant i window hiwindow]
  have hpartial :
      (∑ x ∈ (Finset.range count).image shift, f x) =
        (count : ℝ) * (window : ℝ) ^ (2 * w) := by
    rw [Finset.sum_image (fun i hi j hj hij => hinj hi hj hij)]
    calc
      (∑ i ∈ Finset.range count, f (shift i)) =
          ∑ _i ∈ Finset.range count, (window : ℝ) ^ (2 * w) :=
        Finset.sum_congr rfl hterm
      _ = (count : ℝ) * (window : ℝ) ^ (2 * w) := by simp
  have hnonneg (x : ZMod p) : 0 ≤ f x := by
    dsimp [f]
    positivity
  have hsum :
      (∑ x ∈ (Finset.range count).image shift, f x) ≤
        ∑ x : ZMod p, f x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro x _ _
    exact hnonneg x
  rw [hpartial] at hsum
  simpa only [count, f] using hsum

end SptClassification
