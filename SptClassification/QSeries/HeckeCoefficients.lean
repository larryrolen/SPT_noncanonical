/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.QuadraticTwist
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Square-index Hecke operators on coefficient sequences

The coefficient action of a square-index Hecke operator consists of an upward
index shift, a diagonal term, and a downward shift that is zero at nonintegral
indices. The Euler derivative on exponents `r/24` intertwines the two weight
normalizations. These are coefficient identities; modularity is a separate fact.
-/

public section

namespace SptClassification.QSeries

/-- The downward square-index shift, extended by zero at nonintegral indices. -/
def squareDown {K : Type*} [Zero K] (p : ℕ) (A : ℤ → K) (r : ℤ) : K :=
  if (p : ℤ) ^ 2 ∣ r then A (r / (p : ℤ) ^ 2) else 0

/-- The downward shift uses the quotient exactly when the square divides the index. -/
theorem squareDown_apply {K : Type*} [Zero K] (p : ℕ) (A : ℤ → K) (r : ℤ) :
    squareDown p A r =
      if (p : ℤ) ^ 2 ∣ r then A (r / (p : ℤ) ^ 2) else 0 := (rfl)

/-- The Euler derivative for a series with exponents `r/24`. -/
def thetaCoefficients (A : ℤ → ℚ) (r : ℤ) : ℚ := (r : ℚ) / 24 * A r

/-- The Euler derivative acts coefficientwise at the fractional Fourier index. -/
theorem thetaCoefficients_apply (A : ℤ → ℚ) (r : ℤ) :
    thetaCoefficients A r = (r : ℚ) / 24 * A r := (rfl)

/-- The three-term coefficient action with specified diagonal and downward multipliers. -/
def squareHecke {K : Type*} [Semiring K]
    (p : ℕ) (middle : ℤ → K) (last : K) (A : ℤ → K) (r : ℤ) : K :=
  A ((p : ℤ) ^ 2 * r) + middle r * A r + last * squareDown p A r

/-- The three terms of the square-index coefficient action. -/
theorem squareHecke_apply {K : Type*} [Semiring K]
    (p : ℕ) (middle : ℤ → K) (last : K) (A : ℤ → K) (r : ℤ) :
    squareHecke p middle last A r =
      A ((p : ℤ) ^ 2 * r) + middle r * A r + last * squareDown p A r := (rfl)

/-- Square-index Hecke operators preserve any fixed residue class when the
square of the index is one modulo the period. -/
theorem squareHecke_residue_support {K : Type*} [Semiring K]
    (p : ℕ) (N b : ℤ) (hp : (p : ℤ) ^ 2 % N = 1)
    (middle : ℤ → K) (last : K) (A : ℤ → K)
    (hA : ∀ r : ℤ, A r ≠ 0 → r % N = b)
    (r : ℤ) (hr : squareHecke p middle last A r ≠ 0) : r % N = b := by
  by_contra h
  have hzero : ∀ s : ℤ, s % N = r % N → A s = 0 := by
    intro s hs
    by_contra hn
    exact h (hs.symm.trans (hA s hn))
  have hup : A ((p : ℤ) ^ 2 * r) = 0 := by
    apply hzero
    rw [Int.mul_emod, hp, one_mul, Int.emod_emod]
  have hdown : squareDown p A r = 0 := by
    rw [squareDown_apply]
    split_ifs with hd
    · apply hzero
      have heq := Int.mul_ediv_cancel' hd
      have hmod := congrArg (fun x : ℤ => x % N) heq
      simpa only [Int.mul_emod, hp, one_mul, Int.emod_emod] using hmod
    · rfl
  exact hr (by rw [squareHecke_apply, hup, hzero r rfl, hdown]; simp)

/-- Scalar multiplication commutes with the downward index shift. -/
theorem squareDown_smul (p : ℕ) (c : ℚ) (A : ℤ → ℚ) (r : ℤ) :
    squareDown p (fun s => c * A s) r = c * squareDown p A r := by
  unfold squareDown
  split_ifs <;> simp

/-- Scalar multiplication commutes with the three-term Hecke action. -/
theorem squareHecke_smul (p : ℕ) (middle : ℤ → ℚ) (last c : ℚ)
    (A : ℤ → ℚ) (r : ℤ) :
    squareHecke p middle last (fun s => c * A s) r =
      c * squareHecke p middle last A r := by
  simp only [squareHecke, squareDown_smul]
  ring

/-- The derivative of the downward shift has the inverse square-index scaling. -/
theorem squareDown_theta (p : ℕ) (A : ℤ → ℚ) (r : ℤ) :
    (p : ℚ) ^ 2 * squareDown p (thetaCoefficients A) r =
      (r : ℚ) / 24 * squareDown p A r := by
  unfold squareDown
  split_ifs with hdiv
  · have hmul : r / (p : ℤ) ^ 2 * (p : ℤ) ^ 2 = r := Int.ediv_mul_cancel hdiv
    have hcast : ((r / (p : ℤ) ^ 2 : ℤ) : ℚ) * (p : ℚ) ^ 2 = (r : ℚ) := by
      exact_mod_cast hmul
    dsimp [thetaCoefficients]
    calc
      _ = (((r / (p : ℤ) ^ 2 : ℤ) : ℚ) * (p : ℚ) ^ 2) / 24 *
          A (r / (p : ℤ) ^ 2) := by ring
      _ = _ := by rw [hcast]
  · simp

/-- The Euler derivative intertwines the square-index operators in adjacent weights. -/
theorem squareHecke_theta {p : ℕ} (hp : p ≠ 0) (middle : ℤ → ℚ) (last : ℚ)
    (A : ℤ → ℚ) (r : ℤ) :
    squareHecke p middle last (thetaCoefficients A) r =
      (p : ℚ) ^ 2 * thetaCoefficients
        (squareHecke p (fun s => middle s / (p : ℚ) ^ 2) (last / (p : ℚ) ^ 4) A) r := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hdown : squareDown p (thetaCoefficients A) r =
      ((r : ℚ) / 24 * squareDown p A r) / (p : ℚ) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hpq)).mpr
    simpa only [mul_comm] using squareDown_theta p A r
  simp only [squareHecke, thetaCoefficients, hdown, Int.cast_mul, Int.cast_pow,
    Int.cast_natCast]
  field_simp

/-- Coefficientwise agreement on a quadratic-character class is preserved by a Hecke step. -/
theorem squareHecke_congr_on_class {K : Type*} [Semiring K]
    (l : ℕ) [Fact l.Prime] {p : ℕ}
    (hp : ((p : ℤ) : ZMod l) ≠ 0) (middle : ℤ → K) (last : K)
    {A B : ℤ → K} {sign : ℤ}
    (hAB : ∀ r : ℤ, legendreSym l (-r) = sign → A r = B r)
    {r : ℤ} (hr : legendreSym l (-r) = sign) :
    squareHecke p middle last A r = squareHecke p middle last B r := by
  have hup : legendreSym l (-((p : ℤ) ^ 2 * r)) = sign := by
    rw [← mul_neg, SptClassification.legendreSym_mul_square l hp]
    exact hr
  have hdown : squareDown p A r = squareDown p B r := by
    unfold squareDown
    split_ifs with hdiv
    · apply hAB
      have hmul : (p : ℤ) ^ 2 * (r / (p : ℤ) ^ 2) = r := by
        simpa only [mul_comm] using Int.ediv_mul_cancel hdiv
      have heq : (p : ℤ) ^ 2 * -(r / (p : ℤ) ^ 2) = -r := by rw [mul_neg, hmul]
      rw [← SptClassification.legendreSym_mul_square l hp (-(r / (p : ℤ) ^ 2)), heq]
      exact hr
    · rfl
  simp only [squareHecke, hAB _ hup, hAB _ hr, hdown]

/-- The downward shift commutes with a change of coefficient ring. -/
theorem squareDown_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (p : ℕ) (A : ℤ → R) (r : ℤ) :
    f (squareDown p A r) = squareDown p (fun s => f (A s)) r := by
  by_cases h : (p : ℤ) ^ 2 ∣ r <;> simp [squareDown, h]

/-- The coefficient action commutes with reduction by any ring homomorphism. -/
theorem squareHecke_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (p : ℕ) (middle : ℤ → R) (last : R) (A : ℤ → R) (r : ℤ) :
    f (squareHecke p middle last A r) =
      squareHecke p (fun s => f (middle s)) (f last) (fun s => f (A s)) r := by
  simp only [squareHecke, map_add, map_mul, squareDown_map]

end SptClassification.QSeries
