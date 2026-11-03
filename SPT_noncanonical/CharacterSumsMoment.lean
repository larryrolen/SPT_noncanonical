/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSumsCorrelation
import Mathlib.Tactic.Ring

/-!
# The quadratic moment of character ratios

The diagonal and off-diagonal correlations give an exact second-moment identity
for any finite family of distinct shifts. This is the elementary quadratic
moment underlying the character-sum argument in [trevino2012, trevino2017].
-/

public section

namespace SptClassification

/-- A Dirichlet character sends division in the residue field to division of
character values, including the zero denominator. -/
theorem character_apply_div (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (u v : ZMod p) :
    χ (u / v) = χ u * (χ v)⁻¹ := by
  by_cases hv : v = 0
  · simp [hv, MulChar.map_zero χ]
  · have hχv : χ v ≠ 0 :=
      (MulChar.apply_ne_zero_iff).mpr (isUnit_iff_ne_zero.mpr hv)
    have hχvinv : χ v⁻¹ = (χ v)⁻¹ := by
      apply mul_left_cancel₀ hχv
      calc
        χ v * χ v⁻¹ = χ (v * v⁻¹) := (map_mul χ v v⁻¹).symm
        _ = 1 := by simp [hv]
        _ = χ v * (χ v)⁻¹ := (mul_inv_cancel₀ hχv).symm
    calc
      χ (u / v) = χ (u * v⁻¹) := rfl
      _ = χ u * χ v⁻¹ := map_mul χ u v⁻¹
      _ = χ u * (χ v)⁻¹ := by rw [hχvinv]

/-- The diagonal ratio sum omits exactly the zero of its denominator. -/
theorem sum_character_same_shift_ratio (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (a : ZMod p) :
    (∑ x : ZMod p, χ ((x + a) / (x + a))) = (p : ℂ) - 1 := by
  have hshift := Equiv.sum_comp (Equiv.addRight a)
    (fun y : ZMod p => χ (y / y))
  have hpoint (y : ZMod p) : χ (y / y) = if y = 0 then 0 else 1 := by
    by_cases hy : y = 0
    · simp [hy, MulChar.map_zero χ]
    · simp [hy]
  calc
    (∑ x : ZMod p, χ ((x + a) / (x + a))) =
        ∑ y : ZMod p, χ (y / y) := by
      simpa [Equiv.addRight] using hshift
    _ = ∑ y : ZMod p, (if y = 0 then (0 : ℂ) else 1) :=
      Finset.sum_congr rfl (fun y _ => hpoint y)
    _ = (p : ℂ) - 1 := by
      calc
        (∑ y : ZMod p, if y = 0 then (0 : ℂ) else 1) =
            ∑ y : ZMod p, ((1 : ℂ) - if y = 0 then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : y = 0 <;> simp [hy]
        _ = (p : ℂ) - 1 := by
          rw [Finset.sum_sub_distrib]
          simp

/-- The sum over one row of the quadratic ratio moment is the number of
residues outside the shift family. -/
theorem sum_character_ratio_row (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (shifts : Finset (ZMod p)) (a : ZMod p) (ha : a ∈ shifts) :
    (∑ b ∈ shifts, ∑ x : ZMod p, χ ((x + a) / (x + b))) =
      (p : ℂ) - shifts.card := by
  have hentry (b : ZMod p) :
      (∑ x : ZMod p, χ ((x + a) / (x + b))) =
        (if a = b then (p : ℂ) else 0) - 1 := by
    by_cases hab : a = b
    · subst b
      simpa using sum_character_same_shift_ratio p χ a
    · simpa [hab] using sum_character_two_shift_ratio_eq_neg_one p χ hχ a b hab
  calc
    (∑ b ∈ shifts, ∑ x : ZMod p, χ ((x + a) / (x + b))) =
        ∑ b ∈ shifts, ((if a = b then (p : ℂ) else 0) - 1) :=
      Finset.sum_congr rfl (fun b _ => hentry b)
    _ = (p : ℂ) - shifts.card := by
      rw [Finset.sum_sub_distrib]
      simp [ha]

/-- The exact quadratic ratio moment for a finite set of distinct shifts. -/
theorem sum_character_ratio_quadratic_moment (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (shifts : Finset (ZMod p)) :
    (∑ a ∈ shifts, ∑ b ∈ shifts, ∑ x : ZMod p,
      χ ((x + a) / (x + b))) =
      (shifts.card : ℂ) * ((p : ℂ) - shifts.card) := by
  calc
    (∑ a ∈ shifts, ∑ b ∈ shifts, ∑ x : ZMod p,
        χ ((x + a) / (x + b))) =
        ∑ _a ∈ shifts, ((p : ℂ) - shifts.card) :=
      Finset.sum_congr rfl (fun a ha => sum_character_ratio_row p χ hχ shifts a ha)
    _ = (shifts.card : ℂ) * ((p : ℂ) - shifts.card) := by simp; ring

/-- The quadratic moment of a nonprincipal character sum, paired with the
inverse-valued sum, equals `|I| (p - |I|)`. Character values at zero contribute
zero to both factors. -/
theorem sum_character_shift_sums_mul_inverse (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (shifts : Finset (ZMod p)) :
    (∑ x : ZMod p,
      (∑ a ∈ shifts, χ (x + a)) *
        (∑ b ∈ shifts, (χ (x + b))⁻¹)) =
      (shifts.card : ℂ) * ((p : ℂ) - shifts.card) := by
  calc
    (∑ x : ZMod p,
        (∑ a ∈ shifts, χ (x + a)) *
          (∑ b ∈ shifts, (χ (x + b))⁻¹)) =
        ∑ x : ZMod p, ∑ a ∈ shifts, ∑ b ∈ shifts,
          χ ((x + a) / (x + b)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      exact (character_apply_div p χ (x + a) (x + b)).symm
    _ = ∑ a ∈ shifts, ∑ b ∈ shifts, ∑ x : ZMod p,
          χ ((x + a) / (x + b)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = (shifts.card : ℂ) * ((p : ℂ) - shifts.card) :=
      sum_character_ratio_quadratic_moment p χ hχ shifts

end SptClassification
