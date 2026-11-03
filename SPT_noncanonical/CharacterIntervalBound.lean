/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsCorrelation
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.Analysis.Complex.Basic

/-!
# Constant character intervals

These exact lower-bound identities supply the elementary side of the Burgess
comparison for a constant interval [trevino2012, trevino2017]. The quantitative
upper bound for short sums is a separate analytic obligation.
-/

public section

namespace SptClassification

/-- A character constant on at least two consecutive integers takes a nonzero
value there. -/
theorem constant_character_value_ne_zero (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (start : ℤ) (length : ℕ) (c : ℂ)
    (h2 : 2 ≤ length)
    (hconstant : ∀ i : ℕ, i < length → χ ((start : ZMod p) + (i : ZMod p)) = c) :
    c ≠ 0 := by
  by_cases hs : (start : ZMod p) = 0
  · have h₁ := hconstant 1 (lt_of_lt_of_le (by decide : 1 < 2) h2)
    simp [hs] at h₁
    rw [← h₁]
    exact one_ne_zero
  · have h₀ := hconstant 0 (lt_of_lt_of_le (by decide : 0 < 2) h2)
    simp only [Nat.cast_zero, add_zero] at h₀
    rw [← h₀]
    exact (MulChar.apply_ne_zero_iff).mpr (isUnit_iff_ne_zero.mpr hs)

/-- A nonzero value of a finite Dirichlet character has norm one. -/
theorem norm_character_value_eq_one (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (a : ZMod p) (ha : χ a ≠ 0) :
    ‖χ a‖ = 1 := by
  have hunit : IsUnit a := (MulChar.apply_ne_zero_iff).mp ha
  simpa using χ.unit_norm_eq_one hunit.unit

/-- The constant interval sum is exactly its length times the common value. -/
theorem sum_constant_character_interval (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (start : ℤ) (length : ℕ) (c : ℂ)
    (hconstant : ∀ i : ℕ, i < length → χ ((start : ZMod p) + (i : ZMod p)) = c) :
    (∑ i ∈ Finset.range length, χ ((start : ZMod p) + (i : ZMod p))) =
      (length : ℂ) * c := by
  calc
    (∑ i ∈ Finset.range length, χ ((start : ZMod p) + (i : ZMod p))) =
        ∑ i ∈ Finset.range length, c :=
      Finset.sum_congr rfl (fun i hi => hconstant i (Finset.mem_range.mp hi))
    _ = (length : ℂ) * c := by simp

/-- A constant block of length at least two has a sum of norm exactly its
length. -/
theorem norm_sum_constant_character_interval (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (start : ℤ) (length : ℕ) (c : ℂ)
    (h2 : 2 ≤ length)
    (hconstant : ∀ i : ℕ, i < length → χ ((start : ZMod p) + (i : ZMod p)) = c) :
    ‖∑ i ∈ Finset.range length, χ ((start : ZMod p) + (i : ZMod p))‖ = length := by
  have hc := constant_character_value_ne_zero p χ start length c h2 hconstant
  have hnorm : ‖c‖ = 1 := by
    have hvalue := hconstant 0 (lt_of_lt_of_le (by decide : 0 < 2) h2)
    simp only [Nat.cast_zero, add_zero] at hvalue
    rw [← hvalue]
    exact norm_character_value_eq_one p χ _ (by rw [hvalue]; exact hc)
  rw [sum_constant_character_interval p χ start length c hconstant, norm_mul, hnorm]
  simp

end SptClassification
