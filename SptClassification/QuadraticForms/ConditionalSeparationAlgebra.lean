/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.ClassPolynomials
import Mathlib.Tactic

/-!
# Algebra of two oriented CM actions

The restriction to the cyclic level-six subgroup belongs to the integral
endomorphism order.  The ambient rational endomorphism algebra is a division
algebra; it does not have a restriction map to `ZMod 6`.

We follow the algebraic step of [rolen2026canonical], Lemma 5.2.
-/

@[expose] public section

namespace SptClassification
namespace ConditionalCM

/-- An integral preserving order, its rational division algebra, and the
action on the cyclic subgroup of order six. -/
structure PreservingOrder (O D : Type*) [Ring O] [DivisionRing D] where
  intoDivision : O →+* D
  intoDivision_injective : Function.Injective intoDivision
  restriction : O →+* ZMod 6

/-- The two roots of the CM polynomial act on the cyclic level-six subgroup
through disjoint orientation sets. -/
theorem orientations_disjoint (a b : ZMod 6)
    (ha : a = 0 ∨ a = 1) (hb : b = 3 ∨ b = 4) :
    b ≠ a ∧ b ≠ 1 - a := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst_vars <;> constructor <;> decide

/-- Commuting integral CM actions with the same trace and norm would have
equal or complementary restrictions, contradicting their orientations. -/
theorem oriented_actions_not_commute
    {O D : Type*} [Ring O] [DivisionRing D]
    (order : PreservingOrder O D) (n : ℕ) (α β : O)
    (hα : order.intoDivision α * order.intoDivision α - order.intoDivision α +
      (n : D) = 0)
    (hβ : order.intoDivision β * order.intoDivision β - order.intoDivision β +
      (n : D) = 0)
    (hαres : order.restriction α = 0 ∨ order.restriction α = 1)
    (hβres : order.restriction β = 3 ∨ order.restriction β = 4) :
    order.intoDivision α * order.intoDivision β ≠
      order.intoDivision β * order.intoDivision α := by
  intro hcomm
  let a : D := order.intoDivision α
  let b : D := order.intoDivision β
  have hprod : (a - b) * (a + b - 1) = 0 := by
    have he : (a - b) * (a + b - 1) =
        (a * a - a + (n : D)) - (b * b - b + (n : D)) := by
      dsimp [a, b] at hcomm ⊢
      noncomm_ring [hcomm]
    rw [he]
    simp [a, b, hα, hβ]
  obtain ⟨hneq, hcomp⟩ := orientations_disjoint
    (order.restriction α) (order.restriction β) hαres hβres
  rcases mul_eq_zero.mp hprod with h | h
  · have heq : α = β := order.intoDivision_injective (by
      change a = b
      exact sub_eq_zero.mp h)
    exact hneq (congrArg order.restriction heq).symm
  · have heq : β = 1 - α := order.intoDivision_injective (by
      change b = (order.intoDivision (1 - α))
      rw [map_sub, map_one]
      have hs : a + b = 1 := sub_eq_zero.mp h
      calc
        b = a + b - a := by abel
        _ = 1 - a := by rw [hs])
    exact hcomp (by simpa using congrArg order.restriction heq)

/-- A nonscalar element gives an independent pair over the central copy of
the real numbers. -/
theorem nonscalar_pair_coefficients
    {H : Type*} [DivisionRing H] (scalar : ℝ →+* H)
    (hscalar : Function.Injective scalar) (α : H)
    (hα : ∀ r : ℝ, α ≠ scalar r) (r s : ℝ)
    (h : scalar r + scalar s * α = 0) : r = 0 ∧ s = 0 := by
  by_cases hs : s = 0
  · subst s
    have hr : scalar r = 0 := by simpa using h
    exact ⟨hscalar (by simpa using hr), rfl⟩
  · have hsz : scalar s ≠ 0 := by
      intro hz
      exact hs (hscalar (by simpa using hz))
    have hm : scalar s * α = -scalar r := by
      calc
        scalar s * α = (scalar r + scalar s * α) - scalar r := by abel
        _ = -scalar r := by rw [h]; simp
    have he : α = scalar (s⁻¹ * -r) := by
      calc
        α = (scalar s)⁻¹ * (scalar s * α) := by simp [hsz]
        _ = (scalar s)⁻¹ * (-scalar r) := by rw [hm]
        _ = scalar (s⁻¹ * -r) := by simp [map_mul, map_inv₀]
    exact (hα _ he).elim

/-- Negative CM discriminant makes a quadratic action nonscalar in every
real division algebra. The norm is `(d + 1) / 4`. -/
theorem quadratic_action_nonscalar
    {H : Type*} [DivisionRing H] (scalar : ℝ →+* H)
    (hscalar : Function.Injective scalar) (d n : ℕ)
    (hd : 0 < d) (hn : 4 * n = d + 1) (α : H)
    (hquad : α * α - α + scalar (n : ℝ) = 0) :
    ∀ r : ℝ, α ≠ scalar r := by
  intro r heq
  have hq : scalar (r * r - r + (n : ℝ)) = 0 := by
    rw [map_add, map_sub, map_mul]
    simpa [heq] using hquad
  have hr : r * r - r + (n : ℝ) = 0 := hscalar (by simpa using hq)
  have hnR : 4 * (n : ℝ) = (d : ℝ) + 1 := by exact_mod_cast hn
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  nlinarith [sq_nonneg (r - (1 / 2 : ℝ))]

/-- The key four-vector relation: noncommuting CM actions and a nonscalar
first action force the vectors `1, α, β, αβ` to be real independent. -/
theorem four_action_coefficients
    {H : Type*} [DivisionRing H] (scalar : ℝ →+* H)
    (hscalar : Function.Injective scalar)
    (hcentral : ∀ (r : ℝ) (x : H), scalar r * x = x * scalar r)
    (α β : H) (hα : ∀ r : ℝ, α ≠ scalar r)
    (hnc : α * β ≠ β * α)
    (r s t u : ℝ)
    (hrel : scalar r + scalar s * α + scalar t * β +
      scalar u * (α * β) = 0) :
    r = 0 ∧ s = 0 ∧ t = 0 ∧ u = 0 := by
  let A : H := scalar r + scalar s * α
  let B : H := scalar t + scalar u * α
  have hAB : A + B * β = 0 := by
    dsimp [A, B]
    simpa only [add_mul, mul_assoc, add_assoc] using hrel
  have hAcomm : A * α = α * A := by
    dsimp [A]
    calc
      (scalar r + scalar s * α) * α = scalar r * α + (scalar s * α) * α := by rw [add_mul]
      _ = α * scalar r + (α * scalar s) * α := by rw [hcentral r α, hcentral s α]
      _ = α * (scalar r + scalar s * α) := by rw [mul_add, mul_assoc]
  have hBcomm : B * α = α * B := by
    dsimp [B]
    calc
      (scalar t + scalar u * α) * α = scalar t * α + (scalar u * α) * α := by rw [add_mul]
      _ = α * scalar t + (α * scalar u) * α := by rw [hcentral t α, hcentral u α]
      _ = α * (scalar t + scalar u * α) := by rw [mul_add, mul_assoc]
  by_cases hB : B = 0
  · have htu := nonscalar_pair_coefficients scalar hscalar α hα t u hB
    have hrs := nonscalar_pair_coefficients scalar hscalar α hα r s (by
      simpa [hB] using hAB)
    exact ⟨hrs.1, hrs.2, htu.1, htu.2⟩
  · have hBβ : B * β = -A := by
      calc
        B * β = (A + B * β) - A := by abel
        _ = -A := by rw [hAB]; simp
    have hcomm : B * (β * α) = B * (α * β) := by
      calc
        B * (β * α) = (B * β) * α := by rw [mul_assoc]
        _ = (-A) * α := by rw [hBβ]
        _ = α * (-A) := by simp [hAcomm]
        _ = α * (B * β) := by rw [hBβ]
        _ = (α * B) * β := by rw [mul_assoc]
        _ = (B * α) * β := by rw [hBcomm]
        _ = B * (α * β) := by rw [mul_assoc]
    exact (hnc (mul_left_cancel₀ hB hcomm).symm).elim

end ConditionalCM
end SptClassification
