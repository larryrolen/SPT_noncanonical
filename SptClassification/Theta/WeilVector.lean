/- Assembled by AxiomProver. -/

module

public import SptClassification.Theta.DiscriminantForm
public import SptClassification.Arithmetic.CharacterTwelve

/-!
# The distinguished vector in the discriminant group algebra

The vector `e₁ - e₅ - e₇ + e₁₁` of [rolenManuscript, lines 339–342]
is represented by its coefficient function on `ℤ/12ℤ`. Its support lies
entirely over the quadratic value `1/24`. The eta-multiplier assertion for
the full Weil representation is a subsequent analytic and representation
theoretic proof obligation.
-/

public section

namespace SptClassification
namespace Theta

/-- The standard basis vector of the group algebra on the discriminant group. -/
@[expose]
def basisVector (r : ZMod 12) : ZMod 12 → ℤ :=
  fun s => if s = r then 1 else 0

/-- The input vector `e₁ - e₅ - e₇ + e₁₁` with the manuscript signs. -/
@[expose]
def weilInputVector : ZMod 12 → ℤ :=
  basisVector 1 - basisVector 5 - basisVector 7 + basisVector 11

theorem weilInputVector_eq_character (r : ZMod 12) :
    weilInputVector r = characterTwelveResidue r := by
  fin_cases r <;> decide +kernel

theorem weilInputVector_quadratic_support {r : ZMod 12}
    (hr : weilInputVector r ≠ 0) : discriminantQuadratic r = 1 := by
  fin_cases r <;> first
    | decide +kernel
    | exact False.elim (hr (by decide +kernel))

theorem weilInputVector_neg (r : ZMod 12) :
    weilInputVector (-r) = weilInputVector r := by
  rw [weilInputVector_eq_character, weilInputVector_eq_character]
  fin_cases r <;> decide +kernel

/-- The distinguished integral vector, viewed in a coefficient ring. -/
@[expose]
def weilInputVectorAs (R : Type*) [Ring R] (r : ZMod 12) : R :=
  weilInputVector r

/-- The diagonal operator associated with a chosen phase on quadratic classes.
The actual Weil `T` operator is obtained by choosing its complex phase. -/
def quadraticDiagonal (R : Type*) [Ring R] (phase : ZMod 24 → R)
    (f : ZMod 12 → R) : ZMod 12 → R :=
  fun r => phase (discriminantQuadratic r) * f r

/-- Every quadratic diagonal phase acts on the input vector by its value at `1/24`.
This is the finite algebraic part of the Weil `T` eigenvector calculation. -/
theorem quadraticDiagonal_weilInputVector (R : Type*) [Ring R]
    (phase : ZMod 24 → R) :
    quadraticDiagonal R phase (weilInputVectorAs R) =
      fun r => phase 1 * weilInputVectorAs R r := by
  funext r
  by_cases hr : weilInputVector r = 0
  · simp [quadraticDiagonal, weilInputVectorAs, hr]
  · rw [quadraticDiagonal, weilInputVector_quadratic_support hr]

end Theta
end SptClassification
