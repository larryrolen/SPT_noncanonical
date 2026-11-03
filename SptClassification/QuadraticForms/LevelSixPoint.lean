/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixWeierstrass
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

/-!
# A point of order six on the integral level-six family

The displayed point and its first three multiples construct the cyclic level
subgroup on every nonsingular fiber. All proofs use the actual affine group
law. Identifying this marked family with the eta coordinate is a separate
moduli assertion.
-/

public section
namespace SptClassification.LevelSixWeierstrass
open WeierstrassCurve.Affine
variable {K : Type*} [Field K]

theorem parameter_ne_zero (t : K) (hΔ : (curve t).Δ ≠ 0) :
    t ≠ 0 ∧ t + 8 ≠ 0 ∧ t + 9 ≠ 0 := by
  rw [curve_discriminant] at hΔ
  have h := (mul_ne_zero_iff.mp hΔ)
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  exact ⟨by simpa using h''.2, by simpa using h'.2,
    by simpa using h.2⟩

theorem a₃_ne_zero (t : K) (hΔ : (curve t).Δ ≠ 0) :
    72 * t * (t + 9) * (t + 8) ≠ 0 := by
  have hp := parameter_ne_zero t hΔ
  have h23 : (2 : K) ≠ 0 ∧ (3 : K) ≠ 0 := by
    rw [curve_discriminant] at hΔ
    have h := ((mul_ne_zero_iff.mp ((mul_ne_zero_iff.mp
      ((mul_ne_zero_iff.mp hΔ).1)).1)).1)
    exact ⟨by simpa using (mul_ne_zero_iff.mp h).1,
      by simpa using (mul_ne_zero_iff.mp h).2⟩
  have h72 : (72 : K) ≠ 0 := by
    have he : (72 : K) = 2 ^ 3 * 3 ^ 2 := by norm_num
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ h23.1) (pow_ne_zero _ h23.2)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h72 hp.1) hp.2.2) hp.2.1

theorem origin_nonsingular (t : K) (hΔ : (curve t).Δ ≠ 0) :
    (curve t).toAffine.Nonsingular 0 0 := by
  rw [nonsingular_iff, equation_iff]
  refine ⟨by simp [WeierstrassCurve.toAffine, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆], Or.inr ?_⟩
  simpa [WeierstrassCurve.toAffine, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆] using neg_ne_zero.mpr (a₃_ne_zero t hΔ)

variable [DecidableEq K]

/-- The rational point `(0,0)` on the integral level-six equation. -/
def sixPoint (t : K) (hΔ : (curve t).Δ ≠ 0) : (curve t).toAffine.Point :=
  .some 0 0 (origin_nonsingular t hΔ)

theorem sixPoint_eq (t : K) (hΔ : (curve t).Δ ≠ 0) :
    sixPoint t hΔ = .some 0 0 (origin_nonsingular t hΔ) := (rfl)

theorem sixPoint_double (t : K) (hΔ : (curve t).Δ ≠ 0) :
    ∃ h : (curve t).toAffine.Nonsingular (-8 * t * (t + 9)) (8 * t ^ 2 * (t + 9)),
      2 • sixPoint t hΔ = .some _ _ h := by
  have hy : (0 : K) ≠ (curve t).toAffine.negY 0 0 := by
    simpa [negY, WeierstrassCurve.toAffine, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆] using neg_ne_zero.mpr (a₃_ne_zero t hΔ)
  have hsum := Point.add_self_of_Y_ne (h₁ := origin_nonsingular t hΔ) hy
  have hs : (curve t).toAffine.slope 0 0 0 0 = 0 := by
    simp [slope, WeierstrassCurve.toAffine, curve_a₁, curve_a₂, curve_a₃, curve_a₄]
  have hx : (curve t).toAffine.addX 0 0 ((curve t).toAffine.slope 0 0 0 0) =
      -8 * t * (t + 9) := by
    rw [hs]
    simp [addX, WeierstrassCurve.toAffine, curve_a₁, curve_a₂]
  have hy' : (curve t).toAffine.addY 0 0 0 ((curve t).toAffine.slope 0 0 0 0) =
      8 * t ^ 2 * (t + 9) := by
    rw [hs]
    simp [addY, negY, negAddY, addX, WeierstrassCurve.toAffine,
      curve_a₁, curve_a₂, curve_a₃]
    ring
  simp only [hx, hy'] at hsum
  exact ⟨_, by simpa only [two_nsmul, sixPoint] using hsum⟩

theorem sixPoint_triple (t : K) (hΔ : (curve t).Δ ≠ 0) :
    ∃ h : (curve t).toAffine.Nonsingular (-9 * t * (t + 8)) (9 * t ^ 2 * (t + 8)),
      3 • sixPoint t hΔ = .some _ _ h := by
  obtain ⟨h2, he2⟩ := sixPoint_double t hΔ
  have hx : (0 : K) ≠ -8 * t * (t + 9) := by
    intro he
    have ha : 8 * t * (t + 9) = 0 := by linear_combination he
    apply a₃_ne_zero t hΔ
    calc
      72 * t * (t + 9) * (t + 8) = 9 * (8 * t * (t + 9)) * (t + 8) := by ring
      _ = 0 := by rw [ha]; ring
  have hsum := Point.add_of_X_ne (h₁ := origin_nonsingular t hΔ) (h₂ := h2) hx
  have hs : (curve t).toAffine.slope 0 (-8 * t * (t + 9)) 0 (8 * t ^ 2 * (t + 9)) =
      -t := by
    simp only [slope, hx, ite_false]
    rw [div_eq_iff (sub_ne_zero.mpr hx)]
    ring
  have hx3 : (curve t).toAffine.addX 0 (-8 * t * (t + 9))
      ((curve t).toAffine.slope 0 (-8 * t * (t + 9)) 0 (8 * t ^ 2 * (t + 9))) =
      -9 * t * (t + 8) := by
    rw [hs]
    simp only [addX, WeierstrassCurve.toAffine, curve_a₁, curve_a₂]
    ring
  have hy3 : (curve t).toAffine.addY 0 (-8 * t * (t + 9)) 0
      ((curve t).toAffine.slope 0 (-8 * t * (t + 9)) 0 (8 * t ^ 2 * (t + 9))) =
      9 * t ^ 2 * (t + 8) := by
    rw [hs]
    simp only [addY, negY, negAddY, addX, WeierstrassCurve.toAffine,
      curve_a₁, curve_a₂, curve_a₃]
    ring
  simp only [hx3, hy3] at hsum
  exact ⟨_, by
    rw [show (3 : ℕ) = 1 + 2 from rfl, add_nsmul, one_nsmul, he2]
    exact hsum⟩

theorem sixPoint_six_nsmul (t : K) (hΔ : (curve t).Δ ≠ 0) :
    6 • sixPoint t hΔ = 0 := by
  obtain ⟨h3, he3⟩ := sixPoint_triple t hΔ
  have hn : -((3 : ℕ) • sixPoint t hΔ) = (3 : ℕ) • sixPoint t hΔ := by
    rw [he3, Point.neg_some, Point.some.injEq]
    constructor
    · rfl
    · simp only [negY, WeierstrassCurve.toAffine, curve_a₁, curve_a₃]
      ring
  rw [show (6 : ℕ) = 3 + 3 from rfl, add_nsmul]
  calc
    _ = -((3 : ℕ) • sixPoint t hΔ) + (3 : ℕ) • sixPoint t hΔ := congrArg (· + (3 : ℕ) • sixPoint t hΔ) hn.symm
    _ = 0 := neg_add_cancel _

theorem sixPoint_order (t : K) (hΔ : (curve t).Δ ≠ 0) :
    addOrderOf (sixPoint t hΔ) = 6 := by
  have h1 : sixPoint t hΔ ≠ 0 := by
    exact Point.some_ne_zero _
  have h2 : 2 • sixPoint t hΔ ≠ 0 := by
    obtain ⟨_, he⟩ := sixPoint_double t hΔ
    rw [he]
    exact Point.some_ne_zero _
  have h3 : 3 • sixPoint t hΔ ≠ 0 := by
    obtain ⟨_, he⟩ := sixPoint_triple t hΔ
    rw [he]
    exact Point.some_ne_zero _
  have hdvd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr (sixPoint_six_nsmul t hΔ)
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hdvd
  interval_cases ho : addOrderOf (sixPoint t hΔ) <;> simp_all only [Nat.zero_dvd, Nat.reduceDvd, Nat.reduceEqDiff]
  · exact h1 (by simpa [ho] using (addOrderOf_nsmul_eq_zero (sixPoint t hΔ)))
  · exact h2 (by simpa [ho] using (addOrderOf_nsmul_eq_zero (sixPoint t hΔ)))
  · exact h3 (by simpa [ho] using (addOrderOf_nsmul_eq_zero (sixPoint t hΔ)))

/-- The cyclic subgroup generated by the displayed point. -/
def sixSubgroup (t : K) (hΔ : (curve t).Δ ≠ 0) :
    AddSubgroup (curve t).toAffine.Point :=
  AddSubgroup.zmultiples (sixPoint t hΔ)

theorem sixPoint_nsmul_eq_zero (t : K) (hΔ : (curve t).Δ ≠ 0) (n : ℕ) :
    n • sixPoint t hΔ = 0 ↔ 6 ∣ n := by
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, sixPoint_order]

/-- This is a cyclic subgroup of order six, including in positive characteristic. -/
theorem sixSubgroup_card (t : K) (hΔ : (curve t).Δ ≠ 0) :
    Nat.card (sixSubgroup t hΔ) = 6 := by
  rw [sixSubgroup, Nat.card_zmultiples, sixPoint_order]

end SptClassification.LevelSixWeierstrass
