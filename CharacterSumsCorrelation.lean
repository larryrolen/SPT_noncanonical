/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterSums
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Correlations of finite multiplicative characters

The fractional-linear change of variables gives the exact two-shift
correlation identity. This is the quadratic-moment base case in the
character-sum method used by Treviño [trevino2012, trevino2017].
-/

public section

namespace SptClassification

/-- Inversion permutes a prime residue field, including zero. -/
private def residueInverseEquiv (p : ℕ) [Fact p.Prime] : ZMod p ≃ ZMod p where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := inv_inv x
  right_inv x := inv_inv x

/-- Multiplication by a nonzero residue permutes the residue field. -/
private def residueScaleEquiv (p : ℕ) [Fact p.Prime]
    (t : ZMod p) (ht : t ≠ 0) : ZMod p ≃ ZMod p where
  toFun x := t * x
  invFun x := t⁻¹ * x
  left_inv x := by
    simp [← mul_assoc, inv_mul_cancel₀ ht]
  right_inv x := by
    simp [← mul_assoc, mul_inv_cancel₀ ht]

/-- The mean remains zero after inversion, scaling, and translation. -/
theorem sum_character_affine_inverse_eq_zero (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (a t : ZMod p) (ht : t ≠ 0) :
    (∑ x : ZMod p, χ (a + t * x⁻¹)) = 0 := by
  have hinv := (residueInverseEquiv p).sum_comp (fun x : ZMod p => χ (a + t * x))
  have hscale := (residueScaleEquiv p t ht).sum_comp (fun x : ZMod p => χ (a + x))
  calc
    (∑ x : ZMod p, χ (a + t * x⁻¹)) = ∑ x : ZMod p, χ (a + t * x) := by
      simpa [residueInverseEquiv] using hinv
    _ = ∑ x : ZMod p, χ (a + x) := by
      simpa [residueScaleEquiv] using hscale
    _ = 0 := by
      simpa only [add_comm] using sum_character_translate_eq_zero p χ hχ a

/-- The fractional-linear two-point character sum has the exact value `-1`.
The zero denominator contributes zero, while inversion and scaling permute the
remaining residues. -/
theorem sum_character_ratio_eq_neg_one (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (t : ZMod p) (ht : t ≠ 0) :
    (∑ y : ZMod p, χ ((y + t) / y)) = -1 := by
  have hpoint (y : ZMod p) :
      χ ((y + t) / y) = χ (1 + t * y⁻¹) - (if y = 0 then 1 else 0) := by
    by_cases hy : y = 0
    · simp [hy, MulChar.map_zero χ]
    · have hdiv : (y + t) / y = 1 + t * y⁻¹ := by
        field_simp [hy]
      simp [hy, hdiv]
  calc
    (∑ y : ZMod p, χ ((y + t) / y)) =
        ∑ y : ZMod p, (χ (1 + t * y⁻¹) - (if y = 0 then 1 else 0)) :=
      Finset.sum_congr rfl (fun y _ => hpoint y)
    _ = (∑ y : ZMod p, χ (1 + t * y⁻¹)) - 1 := by
      rw [Finset.sum_sub_distrib]
      simp
    _ = -1 := by
      rw [sum_character_affine_inverse_eq_zero p χ hχ 1 t ht]
      ring

/-- Distinct shifts of a nonprincipal character have the exact rational
correlation `-1` over the residue field. -/
theorem sum_character_two_shift_ratio_eq_neg_one (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (a b : ZMod p) (hab : a ≠ b) :
    (∑ x : ZMod p, χ ((x + a) / (x + b))) = -1 := by
  let t := a - b
  have ht : t ≠ 0 := sub_ne_zero.mpr hab
  have hsum := Equiv.sum_comp (Equiv.addRight b)
    (fun y : ZMod p => χ ((y + t) / y))
  have hratio := sum_character_ratio_eq_neg_one p χ hχ t ht
  simpa [Equiv.addRight, t, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using hsum.trans hratio

end SptClassification
