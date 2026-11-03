/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixModuliCoordinate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Evaluation of the geometric coordinate on the explicit family

The constructed moduli coordinate returns the displayed parameter, including
on nonsingular residue fibers. This is an algebraic statement; analytic eta
identification and CM-action specialization remain separate.
-/

public section

namespace SptClassification.LevelSixWeierstrass

variable {F : Type*} [Field F]

/-- Nonsingular integral-family parameters give nonsingular Tate parameters. -/
theorem tateParameter_regular (t : F) (h6 : (6 : F) ≠ 0)
    (hΔ : (curve t).Δ ≠ 0) : (tateCurve (tateParameter t)).Δ ≠ 0 := by
  have h23 : (2 : F) * 3 ≠ 0 := by norm_num; exact h6
  have h2 := (mul_ne_zero_iff.mp h23).1
  have h3 := (mul_ne_zero_iff.mp h23).2
  have h8 : (8 : F) ≠ 0 := by
    convert pow_ne_zero 3 h2 using 1 <;> norm_num
  have h9 : (9 : F) ≠ 0 := by
    convert pow_ne_zero 2 h3 using 1 <;> norm_num
  obtain ⟨ht, ht8, ht9⟩ := parameter_ne_zero t hΔ
  have hc : tateParameter t ≠ 0 := by
    rw [tateParameter_eq]
    exact div_ne_zero (neg_ne_zero.mpr ht) (mul_ne_zero h9 ht8)
  have hc1 : tateParameter t + 1 ≠ 0 := by
    intro h
    rw [tateParameter_eq] at h
    field_simp [h9, ht8] at h
    apply mul_ne_zero h8 ht9
    linear_combination h
  have hc9 : 9 * tateParameter t + 1 ≠ 0 := by
    intro h
    rw [tateParameter_eq] at h
    field_simp [h9, ht8] at h
    apply h8
    linear_combination h
  rw [tateCurve_discriminant]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hc1)) hc9

variable [DecidableEq F] [IsAlgClosed F]

/-- The explicit family with its actual point of exact order six. Exposing
the structure keeps its dependent curve and point types available to transport. -/
@[expose] def pair (t : F) (hΔ : (curve t).Δ ≠ 0) : LevelSixPair F where
  curve := curve t
  elliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  point := sixPoint t hΔ
  order_six := sixPoint_order t hΔ

/-- Evaluation of the Tate coordinate on the explicit marked family. -/
theorem pair_tateCoordinate (t : F) (h6 : (6 : F) ≠ 0)
    (hΔ : (curve t).Δ ≠ 0) :
    LevelSixPair.tateCoordinate h6 (pair t hΔ) = tateParameter t := by
  have h23 : (2 : F) * 3 ≠ 0 := by norm_num; exact h6
  have h9 : (9 : F) ≠ 0 := by
    convert pow_ne_zero 2 (mul_ne_zero_iff.mp h23).2 using 1 <;> norm_num
  have ht8 := (parameter_ne_zero t hΔ).2.1
  have hc := tateParameter_regular t h6 hΔ
  obtain ⟨e, he⟩ := RationalPointMap.exists_curveEquiv_of_variableChange
    (curve t) (tateCurve (tateParameter t)) ⟨isUnit_iff_ne_zero.mpr hc⟩
    (tateChange t h9 ht8) (tateChange_curve t h9 ht8)
  obtain ⟨hO, heO⟩ := he 0 0 (origin_nonsingular t hΔ)
  have heP : e.toAddEquiv (sixPoint t hΔ) = .some 0 0 (by simpa using hO) := by
    simpa [sixPoint_eq] using heO
  exact LevelSixPair.tateCoordinate_eq_of_model h6 (pair t hΔ) _ hc _ e heP

/-- The geometric moduli coordinate of an explicit nonsingular fiber is its
parameter; this includes all characteristics prime to six. -/
theorem pair_moduliCoordinate (t : F) (h6 : (6 : F) ≠ 0)
    (hΔ : (curve t).Δ ≠ 0) :
    LevelSixPair.moduliCoordinate h6 (pair t hΔ).moduliClass = t := by
  rw [LevelSixPair.moduliCoordinate_eq, LevelSixPair.moduliTateCoordinate_mk,
    pair_tateCoordinate, integralParameter_eq]
  have h23 : (2 : F) * 3 ≠ 0 := by norm_num; exact h6
  have h72 : (72 : F) ≠ 0 := by
    convert mul_ne_zero (pow_ne_zero 3 (mul_ne_zero_iff.mp h23).1)
      (pow_ne_zero 2 (mul_ne_zero_iff.mp h23).2) using 1 <;> norm_num
  exact tate_parameter_inverse t h72 (parameter_ne_zero t hΔ).2.1

end SptClassification.LevelSixWeierstrass
