/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterIntervalMoment
public import SptClassification.Arithmetic.CharacterIntervalBound
import Mathlib.Tactic.Linarith

/-!
# Real quadratic moments of interval character sums

Character values have unit norm away from zero, so inversion is complex
conjugation even at zero. This turns the finite ratio identity into an exact
real mean-square formula [trevino2012, trevino2017].
-/

public section

namespace SptClassification

/-- The inverse of a character value is its complex conjugate, with both sides
zero at a nonunit. -/
theorem character_value_inv_eq_star (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (v : ZMod p) :
    (χ v)⁻¹ = star (χ v) := by
  by_cases hv : χ v = 0
  · simp [hv]
  · have hnorm : ‖χ v‖ = 1 := norm_character_value_eq_one p χ v hv
    have hsq : Complex.normSq (χ v) = 1 := by
      rw [← Complex.sq_norm, hnorm]
      norm_num
    apply mul_left_cancel₀ hv
    rw [mul_inv_cancel₀ hv]
    change 1 = χ v * (starRingEnd ℂ) (χ v)
    rw [Complex.mul_conj, hsq]
    simp

/-- The quadratic character moment is the sum of squared complex norms. -/
theorem sum_character_shift_norm_sq_complex (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (shifts : Finset (ZMod p)) :
    (∑ x : ZMod p,
      ((‖∑ a ∈ shifts, χ (x + a)‖ ^ 2 : ℝ) : ℂ)) =
      (shifts.card : ℂ) * ((p : ℂ) - shifts.card) := by
  have hpoint (x : ZMod p) :
      ((‖∑ a ∈ shifts, χ (x + a)‖ ^ 2 : ℝ) : ℂ) =
        (∑ a ∈ shifts, χ (x + a)) *
          (∑ b ∈ shifts, (χ (x + b))⁻¹) := by
    have hstar :
        (∑ b ∈ shifts, (χ (x + b))⁻¹) =
          (starRingEnd ℂ) (∑ b ∈ shifts, χ (x + b)) := by
      simp_rw [character_value_inv_eq_star p χ]
      change (∑ b ∈ shifts, (starRingEnd ℂ) (χ (x + b))) =
        (starRingEnd ℂ) (∑ b ∈ shifts, χ (x + b))
      rw [map_sum]
    rw [hstar]
    rw [Complex.mul_conj]
    rw [Complex.sq_norm]
  calc
    (∑ x : ZMod p,
        ((‖∑ a ∈ shifts, χ (x + a)‖ ^ 2 : ℝ) : ℂ)) =
        ∑ x : ZMod p,
          (∑ a ∈ shifts, χ (x + a)) *
            (∑ b ∈ shifts, (χ (x + b))⁻¹) :=
      Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = (shifts.card : ℂ) * ((p : ℂ) - shifts.card) :=
      sum_character_shift_sums_mul_inverse p χ hχ shifts

/-- The real quadratic moment of a character over an arbitrary finite shift
family. -/
theorem sum_character_shift_norm_sq (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (shifts : Finset (ZMod p)) :
    (∑ x : ZMod p,
      ‖∑ a ∈ shifts, χ (x + a)‖ ^ 2) =
      (shifts.card : ℝ) * ((p : ℝ) - shifts.card) := by
  exact_mod_cast sum_character_shift_norm_sq_complex p χ hχ shifts

/-- For consecutive shifts, the exact mean square depends only on the
interval length and prime modulus. -/
theorem sum_character_interval_norm_sq (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (length : ℕ) (hlength : length ≤ p) :
    (∑ x : ZMod p,
      ‖∑ a ∈ intervalResidues p length, χ (x + a)‖ ^ 2) =
      (length : ℝ) * ((p : ℝ) - length) := by
  simpa [intervalResidues_card p length hlength] using
    sum_character_shift_norm_sq p χ hχ (intervalResidues p length)

/-- The quadratic moment already rules out a nonprincipal character being
constant on more than half of the residue classes in a consecutive block.
This elementary bound is only a preliminary step toward [trevino2017]. -/
theorem two_mul_constant_character_interval_le (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (start : ℤ) (length : ℕ) (c : ℂ)
    (hconstant : ∀ i : ℕ, i < length →
      χ ((start : ZMod p) + (i : ZMod p)) = c) :
    2 * length ≤ p := by
  by_cases h2 : 2 ≤ length
  · have hlength : length ≤ p :=
      (constant_character_interval_lt_modulus p χ start length c hconstant).le
    have hnorm :
        ‖∑ a ∈ intervalResidues p length,
          χ ((start : ZMod p) + a)‖ = length := by
      rw [sum_character_intervalResidues_eq_range p χ
        (start : ZMod p) length hlength]
      exact norm_sum_constant_character_interval p χ start length c h2 hconstant
    let f : ZMod p → ℝ := fun x =>
      ‖∑ a ∈ intervalResidues p length, χ (x + a)‖ ^ 2
    have hnonneg :
        0 ≤ ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase (start : ZMod p), f x :=
      Finset.sum_nonneg (fun x _ => sq_nonneg _)
    have hdecomp := Finset.sum_erase_add
      (Finset.univ : Finset (ZMod p)) f
      (Finset.mem_univ (start : ZMod p))
    have hle : f (start : ZMod p) ≤ ∑ x : ZMod p, f x := by
      rw [← hdecomp]
      exact le_add_of_nonneg_left hnonneg
    dsimp [f] at hle
    rw [hnorm, sum_character_interval_norm_sq p χ hχ length hlength] at hle
    have hpositive : (0 : ℝ) < length := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) h2)
    have hreal : (2 : ℝ) * length ≤ p := by
      nlinarith [hle, hpositive]
    exact_mod_cast hreal
  · have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega

end SptClassification
