/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsHigherMoment

/-!
# Diagonal correlations in higher character moments

When the numerator and denominator tuples agree, the quotient character is
one away from the roots of their common product. The root count is the number
of distinct shifts in the tuple [trevino2012, trevino2017].
-/

public section

namespace SptClassification

/-- The roots of a product of shifted linear factors are exactly the negatives
of the shifts appearing in the tuple. -/
theorem shift_product_zero_iff (p : ℕ) [Fact p.Prime]
    {ι : Type*} (s : Finset ι) (u : ι → ZMod p) (x : ZMod p) :
    (∏ i ∈ s, (x + u i)) = 0 ↔
      x ∈ s.image (fun i => -u i) := by
  simp only [Finset.prod_eq_zero_iff, Finset.mem_image,
    add_eq_zero_iff_eq_neg]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, h.symm⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, hi, h.symm⟩

/-- A diagonal higher-moment correlation has the exact value `p` minus the
number of distinct roots, even when shifts repeat. -/
theorem sum_character_tuple_self_ratio (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) {ι : Type*} (s : Finset ι)
    (u : ι → ZMod p) :
    (∑ x : ZMod p,
      χ ((∏ i ∈ s, (x + u i)) / (∏ i ∈ s, (x + u i)))) =
      (p : ℂ) - ((s.image (fun i => -u i)).card : ℂ) := by
  have hroots :
      (Finset.univ.filter (fun x : ZMod p =>
        (∏ i ∈ s, (x + u i)) = 0)) =
        s.image (fun i => -u i) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact shift_product_zero_iff p s u x
  rw [sum_character_self_ratio p χ (fun x => ∏ i ∈ s, (x + u i)), hroots]

/-- Reordering the shifts of a tuple does not change its product of linear
factors. This identifies permutation diagonals in a higher moment. -/
theorem shift_product_perm (p w : ℕ) [Fact p.Prime]
    (u : Fin w → ZMod p) (σ : Equiv.Perm (Fin w)) (x : ZMod p) :
    (∏ i : Fin w, (x + u (σ i))) = ∏ i : Fin w, (x + u i) := by
  simpa using (Equiv.prod_comp σ (fun i : Fin w => x + u i))

/-- A tuple paired with a permutation of itself has the same exact complete
correlation as a self-paired tuple. Repeated shifts contribute one missing
residue each, irrespective of their multiplicities. -/
theorem sum_character_tuple_perm_ratio (p w : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (u : Fin w → ZMod p)
    (σ : Equiv.Perm (Fin w)) :
    (∑ x : ZMod p,
      χ ((∏ i : Fin w, (x + u i)) /
        (∏ i : Fin w, (x + u (σ i))))) =
      (p : ℂ) - (((Finset.univ : Finset (Fin w)).image
        (fun i => -u i)).card : ℂ) := by
  have hprod (x : ZMod p) :
      (∏ i : Fin w, (x + u (σ i))) = ∏ i : Fin w, (x + u i) :=
    shift_product_perm p w u σ x
  simp_rw [hprod]
  simpa only [Finset.prod_attach_univ] using
    sum_character_tuple_self_ratio p χ (Finset.univ : Finset (Fin w)) u

/-- Permutation diagonals in a `2w`th moment are parameterized by one
`w`-tuple and one permutation. Their number is at most the resulting product
of cardinalities; different permutations can give the same pair when a shift
repeats [trevino2012]. -/
theorem card_permutation_diagonals_le (p w : ℕ) [Fact p.Prime]
    (shifts : Finset (ZMod p)) :
    let tuples := (Finset.univ : Finset (Fin w)).pi (fun _ => shifts)
    let perms := (Finset.univ : Finset (Equiv.Perm (Fin w)))
    (((tuples.product perms).image fun pair =>
      (pair.1, fun i => pair.1 (pair.2 i) (Finset.mem_univ _))).card) ≤
      tuples.card * perms.card := by
  intro tuples perms
  exact (Finset.card_image_le).trans (Finset.card_product tuples perms).le

/-- There are exactly `|S|^w` ordered `w`-tuples of shifts from a finite set
`S`. -/
theorem card_character_shift_tuples (p w : ℕ) [Fact p.Prime]
    (shifts : Finset (ZMod p)) :
    ((Finset.univ : Finset (Fin w)).pi (fun _ => shifts)).card =
      shifts.card ^ w := by
  simp [Finset.card_pi]

/-- An explicit factorial bound for the permutation-diagonal contribution. -/
theorem card_permutation_diagonals_le_factorial (p w : ℕ) [Fact p.Prime]
    (shifts : Finset (ZMod p)) :
    let tuples := (Finset.univ : Finset (Fin w)).pi (fun _ => shifts)
    let perms := (Finset.univ : Finset (Equiv.Perm (Fin w)))
    (((tuples.product perms).image fun pair =>
      (pair.1, fun i => pair.1 (pair.2 i) (Finset.mem_univ _))).card) ≤
      shifts.card ^ w * w.factorial := by
  simpa [card_character_shift_tuples, Fintype.card_perm] using
    card_permutation_diagonals_le p w shifts

end SptClassification
