/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# An integral Weierstrass family for the level-six coordinate

The coefficients arise from the order-six Tate equation after the substitution
`c = -t / (9 * (t + 8))` and clearing denominators. The invariant identities
below are polynomial calculations, valid over every commutative ring.
Identification of this parameter with the manuscript's eta coordinate is a
separate assertion and is not assumed or claimed here.
-/

public section

namespace SptClassification.LevelSixWeierstrass

variable {R : Type*} [CommRing R]

/-- The integral equation obtained by clearing the Tate parameter denominators. -/
def curve (t : R) : WeierstrassCurve R where
  a₁ := 10 * t + 72
  a₂ := 8 * t * (t + 9)
  a₃ := 72 * t * (t + 9) * (t + 8)
  a₄ := 0
  a₆ := 0

@[simp] theorem curve_a₁ (t : R) : (curve t).a₁ = 10 * t + 72 := (rfl)
@[simp] theorem curve_a₂ (t : R) : (curve t).a₂ = 8 * t * (t + 9) := (rfl)
@[simp] theorem curve_a₃ (t : R) : (curve t).a₃ = 72 * t * (t + 9) * (t + 8) := (rfl)
@[simp] theorem curve_a₄ (t : R) : (curve t).a₄ = 0 := (rfl)
@[simp] theorem curve_a₆ (t : R) : (curve t).a₆ = 0 := (rfl)

theorem curve_c₄ (t : R) :
    (curve t).c₄ = 144 * (t + 12) * (t ^ 3 + 252 * t ^ 2 + 3888 * t + 15552) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curve]
  ring

theorem curve_discriminant (t : R) :
    (curve t).Δ = 2 ^ 12 * 3 ^ 6 * t ^ 6 * (t + 8) ^ 2 * (t + 9) ^ 3 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, curve]
  ring

theorem curve_c₄_zero : (curve (0 : R)).c₄ = 2 ^ 12 * 3 ^ 8 := by
  rw [curve_c₄]
  ring

theorem curve_c₄_neg_eight : (curve (-8 : R)).c₄ = 2 ^ 12 * 3 ^ 2 := by
  rw [curve_c₄]
  ring

theorem curve_c₄_neg_nine : (curve (-9 : R)).c₄ = 2 ^ 4 * 3 ^ 8 := by
  rw [curve_c₄]
  ring

variable {K : Type*} [Field K]

/-- Away from characteristics two and three, the three displayed parameters
are exactly the singular fibers of this equation. -/
theorem discriminant_eq_zero_iff (t : K) (h6 : (6 : K) ≠ 0) :
    (curve t).Δ = 0 ↔ t = 0 ∨ t = -8 ∨ t = -9 := by
  have h23 : (2 : K) * 3 ≠ 0 := by norm_num; exact h6
  have h2 := (mul_ne_zero_iff.mp h23).1
  have h3 := (mul_ne_zero_iff.mp h23).2
  rw [curve_discriminant]
  simp [mul_eq_zero, h2, h3, add_eq_zero_iff_eq_neg, or_assoc]

/-- A finite value of `j`, expressed without division, excludes all singular
fibers. This is the algebraic step needed after reducing integral `t` and `j`.
It requires no splitting-type hypothesis. -/
theorem discriminant_ne_zero_of_j_relation (t j : K) (h6 : (6 : K) ≠ 0)
    (hj : j * (curve t).Δ = (curve t).c₄ ^ 3) : (curve t).Δ ≠ 0 := by
  have h23 : (2 : K) * 3 ≠ 0 := by norm_num; exact h6
  have h2 := (mul_ne_zero_iff.mp h23).1
  have h3 := (mul_ne_zero_iff.mp h23).2
  intro hΔ
  have hc : (curve t).c₄ ^ 3 = 0 := by rw [← hj, hΔ, mul_zero]
  have hc0 : (curve t).c₄ = 0 := by simpa using hc
  rcases (discriminant_eq_zero_iff t h6).mp hΔ with h | h | h
  · subst t
    rw [curve_c₄_zero] at hc0
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3) hc0
  · subst t
    rw [curve_c₄_neg_eight] at hc0
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3) hc0
  · subst t
    rw [curve_c₄_neg_nine] at hc0
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3) hc0

/-- The exact rational-function identity needed to identify this parameter
with a modular coordinate. It is equivalent to the invariant equation. -/
theorem j_relation_iff (t j : K) (h6 : (6 : K) ≠ 0) :
    j * (curve t).Δ = (curve t).c₄ ^ 3 ↔
      j * (t ^ 6 * (t + 8) ^ 2 * (t + 9) ^ 3) =
        (t + 12) ^ 3 * (t ^ 3 + 252 * t ^ 2 + 3888 * t + 15552) ^ 3 := by
  have h23 : (2 : K) * 3 ≠ 0 := by norm_num; exact h6
  have hc : (2 : K) ^ 12 * 3 ^ 6 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero_iff.mp h23).1)
      (pow_ne_zero _ (mul_ne_zero_iff.mp h23).2)
  rw [curve_discriminant, curve_c₄]
  have hl : j * (2 ^ 12 * 3 ^ 6 * t ^ 6 * (t + 8) ^ 2 * (t + 9) ^ 3) =
      (2 ^ 12 * 3 ^ 6) * (j * (t ^ 6 * (t + 8) ^ 2 * (t + 9) ^ 3)) := by ring
  have hr : (144 * (t + 12) * (t ^ 3 + 252 * t ^ 2 + 3888 * t + 15552)) ^ 3 =
      (2 ^ 12 * 3 ^ 6) *
        ((t + 12) ^ 3 * (t ^ 3 + 252 * t ^ 2 + 3888 * t + 15552) ^ 3) := by ring
  rw [hl, hr, mul_right_inj' hc]

/-- The same criterion in mathlib's elliptic-curve predicate. -/
theorem isElliptic_of_j_relation (t j : K) (h6 : (6 : K) ≠ 0)
    (hj : j * (curve t).Δ = (curve t).c₄ ^ 3) : (curve t).IsElliptic := by
  exact ⟨isUnit_iff_ne_zero.mpr (discriminant_ne_zero_of_j_relation t j h6 hj)⟩

/-- Any residue map for which six stays nonzero preserves ellipticity of
this integral equation when its `j`-value is integral in the same ring.
This statement applies equally to ordinary and supersingular reductions. -/
theorem reduction_isElliptic (red : R →+* K) (t j : R) (h6 : (6 : K) ≠ 0)
    (hj : j * (curve t).Δ = (curve t).c₄ ^ 3) : (curve (red t)).IsElliptic := by
  apply isElliptic_of_j_relation (red t) (red j) h6
  simpa only [curve_discriminant, curve_c₄, map_mul, map_pow, map_add,
    map_ofNat] using congrArg red hj

end SptClassification.LevelSixWeierstrass
