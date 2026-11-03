/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsFourthMoment

/-!
# Higher character moments

The finite product-of-sums identity expands every integral power of a short
character sum into tuples of shifts. Treviño's explicit argument uses moments
of several orders [trevino2012, trevino2017].
-/

public section

namespace SptClassification

/-- A character evaluates a quotient of finite products as the quotient of
its values, including the case of a zero factor. -/
theorem character_apply_prod_div (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) {ι : Type*} (s : Finset ι)
    (u v : ι → ZMod p) :
    χ ((∏ i ∈ s, u i) / (∏ i ∈ s, v i)) =
      (∏ i ∈ s, χ (u i)) * (∏ i ∈ s, χ (v i))⁻¹ := by
  rw [character_apply_div]
  simp only [map_prod]

/-- The `w`th power of a finite character sum, written as a sum over ordered
tuples of its shifts. -/
theorem character_sum_pow_eq_tuple_sum (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (shifts : Finset (ZMod p))
    (w : ℕ) (x : ZMod p) :
    (∑ a ∈ shifts, χ (x + a)) ^ w =
      ∑ v ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
        ∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
          χ (x + v i.val i.property) := by
  simpa using
    (Finset.prod_sum (s := (Finset.univ : Finset (Fin w)))
      (t := fun _ => shifts) (f := fun _ a => χ (x + a)))

/-- The same tuple expansion for the inverse values appearing in a norm
moment. -/
theorem character_inverse_sum_pow_eq_tuple_sum (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (shifts : Finset (ZMod p))
    (w : ℕ) (x : ZMod p) :
    (∑ a ∈ shifts, (χ (x + a))⁻¹) ^ w =
      ∑ v ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
        ∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
          (χ (x + v i.val i.property))⁻¹ := by
  simpa using
    (Finset.prod_sum (s := (Finset.univ : Finset (Fin w)))
      (t := fun _ => shifts) (f := fun _ a => (χ (x + a))⁻¹))

/-- An even norm moment factors into the `w`th powers of a character sum and
its inverse-valued companion. The identity includes zeros of the character. -/
theorem character_sum_norm_even (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (shifts : Finset (ZMod p))
    (w : ℕ) (x : ZMod p) :
    ((‖∑ a ∈ shifts, χ (x + a)‖ ^ (2 * w) : ℝ) : ℂ) =
      (∑ a ∈ shifts, χ (x + a)) ^ w *
        (∑ b ∈ shifts, (χ (x + b))⁻¹) ^ w := by
  have hstar :
      (∑ b ∈ shifts, (χ (x + b))⁻¹) =
        (starRingEnd ℂ) (∑ b ∈ shifts, χ (x + b)) := by
    simp_rw [character_value_inv_eq_star p χ]
    change (∑ b ∈ shifts, (starRingEnd ℂ) (χ (x + b))) =
      (starRingEnd ℂ) (∑ b ∈ shifts, χ (x + b))
    rw [map_sum]
  have hsq :
      (((‖∑ a ∈ shifts, χ (x + a)‖ ^ 2 : ℝ) : ℂ)) =
        (∑ a ∈ shifts, χ (x + a)) *
          (∑ b ∈ shifts, (χ (x + b))⁻¹) := by
    rw [hstar, Complex.mul_conj, ← Complex.sq_norm]
  calc
    ((‖∑ a ∈ shifts, χ (x + a)‖ ^ (2 * w) : ℝ) : ℂ) =
        (((‖∑ a ∈ shifts, χ (x + a)‖ ^ 2 : ℝ) : ℂ)) ^ w := by
      rw [pow_mul]
      push_cast
      rfl
    _ = (∑ a ∈ shifts, χ (x + a)) ^ w *
          (∑ b ∈ shifts, (χ (x + b))⁻¹) ^ w := by
      rw [hsq, mul_pow]

/-- Every even character moment is a finite sum of complete rational
character sums. The two tuples encode the numerator and denominator factors;
zero factors are handled by the Dirichlet character itself. -/
theorem sum_character_norm_even_ratio_moment (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (shifts : Finset (ZMod p)) (w : ℕ) :
    (∑ x : ZMod p,
      ((‖∑ a ∈ shifts, χ (x + a)‖ ^ (2 * w) : ℝ) : ℂ)) =
      ∑ u ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
        ∑ v ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
          ∑ x : ZMod p,
            χ ((∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
                  (x + u i.val i.property)) /
                (∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
                  (x + v i.val i.property))) := by
  have hpoint (x : ZMod p) :
      ((‖∑ a ∈ shifts, χ (x + a)‖ ^ (2 * w) : ℝ) : ℂ) =
        ∑ u ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
          ∑ v ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
            χ ((∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
                  (x + u i.val i.property)) /
                (∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
                  (x + v i.val i.property))) := by
    rw [character_sum_norm_even p χ shifts w x,
      character_sum_pow_eq_tuple_sum p χ shifts w x,
      character_inverse_sum_pow_eq_tuple_sum p χ shifts w x]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.prod_inv_distrib]
    exact (character_apply_prod_div p χ
      (Finset.univ : Finset (Fin w)).attach
      (fun i => x + u i.val i.property)
      (fun i => x + v i.val i.property)).symm
  calc
    (∑ x : ZMod p,
      ((‖∑ a ∈ shifts, χ (x + a)‖ ^ (2 * w) : ℝ) : ℂ)) =
        ∑ x : ZMod p,
          ∑ u ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
            ∑ v ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
              χ ((∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
                    (x + u i.val i.property)) /
                  (∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
                    (x + v i.val i.property))) :=
      Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = ∑ u ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
          ∑ v ∈ (Finset.univ : Finset (Fin w)).pi (fun _ => shifts),
            ∑ x : ZMod p,
              χ ((∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
                    (x + u i.val i.property)) /
                  (∏ i ∈ (Finset.univ : Finset (Fin w)).attach,
                    (x + v i.val i.property))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]

end SptClassification
