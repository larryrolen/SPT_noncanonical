/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterIntervalNormMoment

/-!
# Fourth moments of finite character sums

The fourth moment expands into complete character sums of products of two
linear factors. This is the first higher moment needed for the Burgess
argument underlying the corrected interval estimate [trevino2012, trevino2017].
-/

public section

namespace SptClassification

/-- A complete diagonal correlation omits precisely the zeros of its
underlying function. This applies to every product of shifted linear factors
in a higher character moment. -/
theorem sum_character_self_ratio (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (f : ZMod p → ZMod p) :
    (∑ x : ZMod p, χ (f x / f x)) =
      (p : ℂ) - ((Finset.univ.filter (fun x : ZMod p => f x = 0)).card : ℂ) := by
  have hpoint (x : ZMod p) :
      χ (f x / f x) = 1 - if f x = 0 then (1 : ℂ) else 0 := by
    by_cases hx : f x = 0 <;> simp [hx, MulChar.map_zero χ]
  calc
    (∑ x : ZMod p, χ (f x / f x)) =
        ∑ x : ZMod p, (1 - if f x = 0 then (1 : ℂ) else 0) :=
      Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = (p : ℂ) - ((Finset.univ.filter (fun x : ZMod p => f x = 0)).card : ℂ) := by
      rw [Finset.sum_sub_distrib]
      simp

/-- The diagonal correlation for two shifted factors has one exceptional
residue when the shifts coincide and two otherwise. -/
theorem sum_character_two_factor_self_ratio (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (a b : ZMod p) :
    (∑ x : ZMod p,
      χ (((x + a) * (x + b)) / ((x + a) * (x + b)))) =
      (p : ℂ) - (if a = b then 1 else 2) := by
  have hroots :
      (Finset.univ.filter (fun x : ZMod p => (x + a) * (x + b) = 0)) =
        ({-a, -b} : Finset (ZMod p)) := by
    ext x
    simp [mul_eq_zero, add_eq_zero_iff_eq_neg]
  rw [sum_character_self_ratio p χ (fun x => (x + a) * (x + b)), hroots]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab]

/-- The fourth power of the norm of a character sum is its product with two
conjugate copies, including the character's zero values. -/
theorem character_sum_norm_fourth (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (shifts : Finset (ZMod p)) (x : ZMod p) :
    ((‖∑ a ∈ shifts, χ (x + a)‖ ^ 4 : ℝ) : ℂ) =
      ((∑ a ∈ shifts, χ (x + a)) *
        (∑ b ∈ shifts, (χ (x + b))⁻¹)) ^ 2 := by
  have hstar :
      (∑ b ∈ shifts, (χ (x + b))⁻¹) =
        (starRingEnd ℂ) (∑ b ∈ shifts, χ (x + b)) := by
    simp_rw [character_value_inv_eq_star p χ]
    change (∑ b ∈ shifts, (starRingEnd ℂ) (χ (x + b))) =
      (starRingEnd ℂ) (∑ b ∈ shifts, χ (x + b))
    rw [map_sum]
  rw [hstar, Complex.mul_conj]
  rw [← Complex.sq_norm]
  push_cast
  ring

/-- The fourth moment is a sum of complete character sums of rational
functions with two numerator and two denominator factors. -/
theorem sum_character_shift_norm_fourth (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (shifts : Finset (ZMod p)) :
    (∑ x : ZMod p, ((‖∑ a ∈ shifts, χ (x + a)‖ ^ 4 : ℝ) : ℂ)) =
      ∑ a ∈ shifts, ∑ b ∈ shifts, ∑ c ∈ shifts, ∑ d ∈ shifts,
        ∑ x : ZMod p,
          χ (((x + c) * (x + d)) / ((x + a) * (x + b))) := by
  have hpoint (x : ZMod p) :
      ((‖∑ a ∈ shifts, χ (x + a)‖ ^ 4 : ℝ) : ℂ) =
        ∑ a ∈ shifts, ∑ b ∈ shifts, ∑ c ∈ shifts, ∑ d ∈ shifts,
          χ (((x + c) * (x + d)) / ((x + a) * (x + b))) := by
    rw [character_sum_norm_fourth]
    have hfour :
        ((∑ a ∈ shifts, χ (x + a)) *
          (∑ b ∈ shifts, (χ (x + b))⁻¹)) ^ 2 =
          (∑ a ∈ shifts, χ (x + a)) *
          (∑ b ∈ shifts, χ (x + b)) *
          (∑ c ∈ shifts, (χ (x + c))⁻¹) *
          (∑ d ∈ shifts, (χ (x + d))⁻¹) := by ring
    rw [hfour]
    conv_lhs => simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro d _
    rw [character_apply_div]
    simp only [map_mul]
    ring
  calc
    (∑ x : ZMod p, ((‖∑ a ∈ shifts, χ (x + a)‖ ^ 4 : ℝ) : ℂ)) =
        ∑ x : ZMod p, ∑ a ∈ shifts, ∑ b ∈ shifts,
          ∑ c ∈ shifts, ∑ d ∈ shifts,
            χ (((x + c) * (x + d)) / ((x + a) * (x + b))) :=
      Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = ∑ a ∈ shifts, ∑ b ∈ shifts, ∑ c ∈ shifts, ∑ d ∈ shifts,
          ∑ x : ZMod p,
            χ (((x + c) * (x + d)) / ((x + a) * (x + b))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

end SptClassification
