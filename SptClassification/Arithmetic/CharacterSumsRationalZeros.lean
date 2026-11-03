/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsDiagonal

/-!
# Zeros of rational character correlations

A quotient of two products of shifted linear factors vanishes exactly at the
roots of either product. A Dirichlet character modulo a prime vanishes at the
same residues. The union of the two root sets therefore gives the exact
exceptional set in a complete rational character sum [trevino2012].
-/

public section

namespace SptClassification

/-- A complex Dirichlet character modulo a prime vanishes precisely at the
zero residue. -/
theorem character_apply_eq_zero_iff (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (z : ZMod p) :
    χ z = 0 ↔ z = 0 := by
  by_cases hz : z = 0
  · simp [hz, MulChar.map_zero χ]
  · have hχz : χ z ≠ 0 :=
      (MulChar.apply_ne_zero_iff).mpr (isUnit_iff_ne_zero.mpr hz)
    simp [hz, hχz]

/-- The quotient of two finite products is zero exactly when at least one
factor in either product is zero. Division by zero is zero in `ZMod p`. -/
theorem shift_product_ratio_zero_iff (p : ℕ) [Fact p.Prime]
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (u : ι → ZMod p) (v : κ → ZMod p) (x : ZMod p) :
    ((∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j))) = 0 ↔
      x ∈ (s.image fun i => -u i) ∪ (t.image fun j => -v j) := by
  rw [Finset.mem_union, ← shift_product_zero_iff p s u x,
    ← shift_product_zero_iff p t v x]
  by_cases hu : (∏ i ∈ s, (x + u i)) = 0
  · simp [hu]
  · by_cases hv : (∏ j ∈ t, (x + v j)) = 0
    · simp [hv]
    · simp [hu, hv]

/-- The zeros of a rational character correlation are exactly the union of
the numerator and denominator root sets, including repeated shifts. -/
theorem character_shift_product_ratio_zero_iff (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (u : ι → ZMod p) (v : κ → ZMod p) (x : ZMod p) :
    χ ((∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j))) = 0 ↔
      x ∈ (s.image fun i => -u i) ∪ (t.image fun j => -v j) := by
  rw [character_apply_eq_zero_iff p χ,
    shift_product_ratio_zero_iff p s t u v x]

/-- The exact zero count is the number of distinct roots appearing in either
product. -/
theorem card_character_shift_product_ratio_zeros (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (u : ι → ZMod p) (v : κ → ZMod p) :
    (Finset.univ.filter (fun x : ZMod p =>
      χ ((∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j))) = 0)).card =
      ((s.image fun i => -u i) ∪ (t.image fun j => -v j)).card := by
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact character_shift_product_ratio_zero_iff p χ s t u v x

/-- At most one distinct zero is contributed by each linear factor in the
numerator or denominator. -/
theorem card_character_shift_product_ratio_zeros_le (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (u : ι → ZMod p) (v : κ → ZMod p) :
    (Finset.univ.filter (fun x : ZMod p =>
      χ ((∏ i ∈ s, (x + u i)) / (∏ j ∈ t, (x + v j))) = 0)).card ≤
      s.card + t.card := by
  rw [card_character_shift_product_ratio_zeros p χ s t u v]
  calc
    ((s.image fun i => -u i) ∪ (t.image fun j => -v j)).card ≤
        (s.image fun i => -u i).card + (t.image fun j => -v j).card :=
      Finset.card_union_le _ _
    _ ≤ s.card + t.card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le

end SptClassification
