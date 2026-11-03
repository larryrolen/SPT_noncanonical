/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixWeierstrass
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tate coordinates for the integral level-six equation

The change of parameter and the scaling below identify the displayed
Weierstrass equations. They preserve the distinguished affine origin.
These algebraic identities do not identify the parameter with an eta quotient;
that requires the marked modular-curve correspondence.
-/

public section

namespace SptClassification.LevelSixWeierstrass

section Ring

variable {K : Type*} [CommRing K]

/-- The order-six Tate equation, with its distinguished point at `(0,0)`. -/
def tateCurve (c : K) : WeierstrassCurve K where
  a₁ := 1 - c
  a₂ := -c * (c + 1)
  a₃ := -c * (c + 1)
  a₄ := 0
  a₆ := 0

theorem tateCurve_a₁ (c : K) : (tateCurve c).a₁ = 1 - c := (rfl)

theorem tateCurve_a₂ (c : K) : (tateCurve c).a₂ = -c * (c + 1) := (rfl)

theorem tateCurve_a₃ (c : K) : (tateCurve c).a₃ = -c * (c + 1) := (rfl)

theorem tateCurve_a₄ (c : K) : (tateCurve c).a₄ = 0 := (rfl)

theorem tateCurve_a₆ (c : K) : (tateCurve c).a₆ = 0 := (rfl)

theorem tateCurve_c₄ (c : K) :
    (tateCurve c).c₄ = 9 * c ^ 4 + 12 * c ^ 3 + 30 * c ^ 2 + 12 * c + 1 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tateCurve]
  ring

theorem tateCurve_discriminant (c : K) :
    (tateCurve c).Δ = c ^ 6 * (c + 1) ^ 3 * (9 * c + 1) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, tateCurve]
  ring

end Ring

variable {K : Type*} [Field K]

/-- The parameter on the Tate equation corresponding to the integral family. -/
def tateParameter (t : K) : K := -t / (9 * (t + 8))

theorem tateParameter_eq (t : K) : tateParameter t = -t / (9 * (t + 8)) := (rfl)

/-- The scaling from Tate affine coordinates to integral affine coordinates. -/
def tateScale (t : K) : K := 9 * (t + 8)

theorem tateScale_ne_zero (t : K) (h9 : (9 : K) ≠ 0) (h8 : t + 8 ≠ 0) :
    tateScale t ≠ 0 := mul_ne_zero h9 h8

theorem tate_parameter_inverse (t : K) (h72 : (72 : K) ≠ 0) (h8 : t + 8 ≠ 0) :
    -72 * tateParameter t / (9 * tateParameter t + 1) = t := by
  have h9 : (9 : K) ≠ 0 := by
    intro h
    apply h72
    calc (72 : K) = 8 * 9 := by norm_num
         _ = 0 := by rw [h, mul_zero]
  have hden : 9 * tateParameter t + 1 ≠ 0 := by
    intro h
    dsimp [tateParameter] at h
    field_simp [h9, h8] at h
    apply h72
    linear_combination 9 * h
  rw [div_eq_iff hden]
  dsimp [tateParameter]
  field_simp [h9, h8]
  <;> ring

/-- Each coefficient transforms with its Weierstrass weight. -/
theorem tate_coefficient_scaling (t : K) (h9 : (9 : K) ≠ 0) (h8 : t + 8 ≠ 0) :
    tateScale t * (tateCurve (tateParameter t)).a₁ = (curve t).a₁ ∧
    tateScale t ^ 2 * (tateCurve (tateParameter t)).a₂ = (curve t).a₂ ∧
    tateScale t ^ 3 * (tateCurve (tateParameter t)).a₃ = (curve t).a₃ := by
  simp only [curve_a₁, curve_a₂, curve_a₃]
  dsimp [tateScale, tateCurve, tateParameter]
  constructor
  · field_simp [h9, h8]
    <;> ring
  constructor <;> field_simp [h9, h8] <;> ring

/-- The admissible change taking the Tate equation to the integral equation.
Its inverse sends `(x,y)` to `(u²x,u³y)`, where `u = tateScale t`. -/
def tateChange (t : K) (h9 : (9 : K) ≠ 0) (h8 : t + 8 ≠ 0) :
    WeierstrassCurve.VariableChange K :=
  ⟨(Units.mk0 (tateScale t) (tateScale_ne_zero t h9 h8))⁻¹, 0, 0, 0⟩

@[simp] theorem tateChange_r (t : K) (h9 : (9 : K) ≠ 0) (h8 : t + 8 ≠ 0) :
    (tateChange t h9 h8).r = 0 := (rfl)

@[simp] theorem tateChange_t (t : K) (h9 : (9 : K) ≠ 0) (h8 : t + 8 ≠ 0) :
    (tateChange t h9 h8).t = 0 := (rfl)

/-- Equality under mathlib's action of admissible changes of variables. -/
theorem tateChange_curve (t : K) (h9 : (9 : K) ≠ 0) (h8 : t + 8 ≠ 0) :
    tateChange t h9 h8 • tateCurve (tateParameter t) = curve t := by
  obtain ⟨h1, h2, h3⟩ := tate_coefficient_scaling t h9 h8
  ext
  · simpa [WeierstrassCurve.variableChange_a₁, tateChange] using h1
  · simpa [WeierstrassCurve.variableChange_a₂, tateChange] using h2
  · simpa [WeierstrassCurve.variableChange_a₃, tateChange] using h3
  · simp [WeierstrassCurve.variableChange_a₄, tateChange, tateCurve]
  · simp [WeierstrassCurve.variableChange_a₆, tateChange, tateCurve]

/-- The coordinate scaling transports the affine equation and fixes `(0,0)`. -/
theorem tate_affine_equation_iff (t x y : K) (h9 : (9 : K) ≠ 0)
    (h8 : t + 8 ≠ 0) :
    (curve t).toAffine.Equation (tateScale t ^ 2 * x) (tateScale t ^ 3 * y) ↔
      (tateCurve (tateParameter t)).toAffine.Equation x y := by
  obtain ⟨h1, h2, h3⟩ := tate_coefficient_scaling t h9 h8
  rw [WeierstrassCurve.Affine.equation_iff', WeierstrassCurve.Affine.equation_iff']
  change _ = 0 ↔ _ = 0
  rw [← h1, ← h2, ← h3, curve_a₄, curve_a₆]
  have hscale : tateScale t ^ 6 ≠ 0 := pow_ne_zero _ (tateScale_ne_zero t h9 h8)
  have heq :
      (tateScale t ^ 3 * y) ^ 2 +
        (tateScale t * (tateCurve (tateParameter t)).a₁) * (tateScale t ^ 2 * x) *
          (tateScale t ^ 3 * y) +
        (tateScale t ^ 3 * (tateCurve (tateParameter t)).a₃) * (tateScale t ^ 3 * y) -
        ((tateScale t ^ 2 * x) ^ 3 +
          (tateScale t ^ 2 * (tateCurve (tateParameter t)).a₂) *
            (tateScale t ^ 2 * x) ^ 2 + 0 * (tateScale t ^ 2 * x) + 0) =
      tateScale t ^ 6 *
        (y ^ 2 + (tateCurve (tateParameter t)).a₁ * x * y +
          (tateCurve (tateParameter t)).a₃ * y -
          (x ^ 3 + (tateCurve (tateParameter t)).a₂ * x ^ 2 +
            (tateCurve (tateParameter t)).a₄ * x +
            (tateCurve (tateParameter t)).a₆)) := by
    simp only [tateCurve]
    ring
  rw [heq, mul_eq_zero]
  simp only [hscale, false_or]

/-- A coordinate change between nonsingular Tate models that fixes the marked
origin has the same parameter. This algebraic uniqueness statement retains
the coordinate-change data explicitly. -/
theorem tateParameter_eq_of_variableChange (c d : K)
    (hc : (tateCurve c).Δ ≠ 0)
    (C : WeierstrassCurve.VariableChange K)
    (hC : C • tateCurve c = tateCurve d) (hr : C.r = 0) (ht : C.t = 0) :
    c = d := by
  have hb : c * (c + 1) ≠ 0 := by
    rw [tateCurve_discriminant] at hc
    have hc0 : c ≠ 0 := by intro h; simp [h] at hc
    have hc1 : c + 1 ≠ 0 := by intro h; simp [h] at hc
    exact mul_ne_zero hc0 hc1
  have h1 := congrArg WeierstrassCurve.a₁ hC
  have h2 := congrArg WeierstrassCurve.a₂ hC
  have h3 := congrArg WeierstrassCurve.a₃ hC
  have h4 := congrArg WeierstrassCurve.a₄ hC
  simp only [WeierstrassCurve.variableChange_a₁, tateCurve, hr] at h1
  simp only [WeierstrassCurve.variableChange_a₂, tateCurve, hr, ht] at h2
  simp only [WeierstrassCurve.variableChange_a₃, tateCurve, hr, ht] at h3
  simp only [WeierstrassCurve.variableChange_a₄, tateCurve, hr, ht] at h4
  have hs : C.s = 0 := by
    simpa [mul_eq_zero, hb, mul_assoc] using h4
  simp [hs] at h1 h2 h3
  have hu : (C.u : K) = 1 := by
    have he := h2.trans h3.symm
    field_simp at he
    apply (mul_right_cancel₀ hb)
    linear_combination he
  simpa [hu] using h1

end SptClassification.LevelSixWeierstrass
