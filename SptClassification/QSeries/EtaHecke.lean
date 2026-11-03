/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.HeckeCoefficients
public import SptClassification.Arithmetic.CharacterTwelve
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The two eta-multiplier Hecke normalizations

For a prime `p` coprime to six, the middle multiplier is `(12/p)(-r/p)`.
Jacobi symbols let us define the coefficient operators without a dependent
primality argument; on primes they are the usual Legendre symbols.

Repeated primes in a Hecke word are retained. The derivative identity is proved
for these actual compositions rather than a different single-index operator.
-/

public section

namespace SptClassification.QSeries

/-- The common quadratic-character multiplier in the two half-integral weights. -/
def etaHeckeDiagonal (p : ℕ) (r : ℤ) : ℚ :=
  (jacobiSym 12 p : ℚ) * (jacobiSym (-r) p : ℚ)

/-- The eta multiplier is the product of the two Jacobi symbols. -/
theorem etaHeckeDiagonal_apply (p : ℕ) (r : ℤ) :
    etaHeckeDiagonal p r =
      (jacobiSym 12 p : ℚ) * (jacobiSym (-r) p : ℚ) := (rfl)

/-- At an odd prime, the diagonal term has the usual eta-character normalization. -/
theorem etaHeckeDiagonal_eq (p : ℕ) [Fact p.Prime] (hp : Odd p) (r : ℤ) :
    etaHeckeDiagonal p r =
      (characterTwelve (p : ℤ) : ℚ) * (legendreSym p (-r) : ℚ) := by
  rw [etaHeckeDiagonal, characterTwelve_eq_jacobi_of_odd hp,
    jacobiSym.legendreSym.to_jacobiSym]

/-- At the negative square index, the middle Hecke coefficient is exactly
`χ₁₂(p) (m²/p)` in [rolen2026canonical, equation (2.5), PDF p. 3].
The Legendre symbol is zero when `p ∣ m`, including repeated-prime steps. -/
theorem etaHeckeDiagonal_negative_square (p m : ℕ) [Fact p.Prime]
    (hp : Odd p) :
    etaHeckeDiagonal p (-((m : ℤ) ^ 2)) =
      (characterTwelve (p : ℤ) : ℚ) *
        (legendreSym p ((m : ℤ) ^ 2) : ℚ) := by
  simpa only [neg_neg] using
    (etaHeckeDiagonal_eq p hp (-((m : ℤ) ^ 2)))

/-- Separate the index-independent eta factor from the quadratic character.
This is the scalar needed for the signed cusp Gauss row at a prime. -/
theorem etaHeckeDiagonal_eq_character_factor (p : ℕ) [Fact p.Prime]
    (hp : Odd p) (r : ℤ) :
    etaHeckeDiagonal p r =
      ((characterTwelve (p : ℤ) * legendreSym p (-1) : ℤ) : ℚ) *
        (legendreSym p r : ℚ) := by
  have hneg : legendreSym p (-r) =
      legendreSym p (-1) * legendreSym p r := by
    change quadraticChar (ZMod p) ((-r : ℤ) : ZMod p) =
      quadraticChar (ZMod p) ((-1 : ℤ) : ZMod p) *
        quadraticChar (ZMod p) (r : ZMod p)
    rw [show -r = (-1 : ℤ) * r by ring, Int.cast_mul]
    exact map_mul (quadraticChar (ZMod p)) _ _
  rw [etaHeckeDiagonal_eq p hp r, hneg]
  push_cast
  ring

/-- The index-independent scalar in the weight `-1/2` middle Hecke row. -/
def etaHeckeMiddleScalar (p : ℕ) [Fact p.Prime] : ℚ :=
  ((characterTwelve (p : ℤ) * legendreSym p (-1) : ℤ) : ℚ) / (p : ℚ) ^ 2

/-- The rational value of the fixed middle-row Hecke scalar. -/
theorem etaHeckeMiddleScalar_eq (p : ℕ) [Fact p.Prime] :
    etaHeckeMiddleScalar p =
      ((characterTwelve (p : ℤ) * legendreSym p (-1) : ℤ) : ℚ) / (p : ℚ) ^ 2 :=
  (rfl)

/-- The weight `-1/2` middle multiplier is the quadratic character times
the fixed eta and prime-square normalization. -/
theorem etaHeckeDiagonal_div_square (p : ℕ) [Fact p.Prime]
    (hp : Odd p) (r : ℤ) :
    etaHeckeDiagonal p r / (p : ℚ) ^ 2 =
      etaHeckeMiddleScalar p * (legendreSym p r : ℚ) := by
  rw [etaHeckeDiagonal_eq_character_factor p hp r]
  unfold etaHeckeMiddleScalar
  ring

/-- The coefficient action in weight `3/2`. -/
def heckeThreeHalf (p : ℕ) (A : ℤ → ℚ) : ℤ → ℚ :=
  squareHecke p (etaHeckeDiagonal p) (p : ℚ) A

/-- The weight `3/2` action has the common three-term square-index form. -/
theorem heckeThreeHalf_eq_squareHecke (p : ℕ) (A : ℤ → ℚ) :
    heckeThreeHalf p A = squareHecke p (etaHeckeDiagonal p) (p : ℚ) A := (rfl)

/-- The coefficient action in weight `-1/2`. -/
def heckeMinusHalf (p : ℕ) (A : ℤ → ℚ) : ℤ → ℚ :=
  squareHecke p (fun r => etaHeckeDiagonal p r / (p : ℚ) ^ 2)
    (1 / (p : ℚ) ^ 3) A

/-- The weight `-1/2` action with its rational middle and downward factors. -/
theorem heckeMinusHalf_eq_squareHecke (p : ℕ) (A : ℤ → ℚ) :
    heckeMinusHalf p A =
      squareHecke p (fun r => etaHeckeDiagonal p r / (p : ℚ) ^ 2)
        (1 / (p : ℚ) ^ 3) A := (rfl)

/-- The exact derivative relation between the source's two weight normalizations. -/
theorem heckeThreeHalf_theta {p : ℕ} (hp : p ≠ 0) (A : ℤ → ℚ) :
    heckeThreeHalf p (thetaCoefficients A) =
      fun r => (p : ℚ) ^ 2 * thetaCoefficients (heckeMinusHalf p A) r := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hlast : (p : ℚ) / (p : ℚ) ^ 4 = 1 / (p : ℚ) ^ 3 := by field_simp
  funext r
  simpa only [heckeThreeHalf, heckeMinusHalf, hlast] using
    squareHecke_theta hp (etaHeckeDiagonal p) (p : ℚ) A r

/-- A constant factor can be pulled through the weight `3/2` coefficient action. -/
theorem heckeThreeHalf_smul (p : ℕ) (c : ℚ) (A : ℤ → ℚ) :
    heckeThreeHalf p (fun r => c * A r) = fun r => c * heckeThreeHalf p A r := by
  funext r
  exact squareHecke_smul p (etaHeckeDiagonal p) (p : ℚ) c A r

/-- Apply a sequence of weight `3/2` Hecke operators in the listed order. -/
def heckeThreeHalfWord : List ℕ → (ℤ → ℚ) → (ℤ → ℚ)
  | [], A => A
  | p :: ps, A => heckeThreeHalfWord ps (heckeThreeHalf p A)

/-- An empty Hecke word leaves its coefficient row unchanged. -/
theorem heckeThreeHalfWord_nil (A : ℤ → ℚ) :
    heckeThreeHalfWord [] A = A := (rfl)

/-- A Hecke word first applies its head operator. -/
theorem heckeThreeHalfWord_cons (p : ℕ) (ps : List ℕ) (A : ℤ → ℚ) :
    heckeThreeHalfWord (p :: ps) A =
      heckeThreeHalfWord ps (heckeThreeHalf p A) := (rfl)

/-- Apply the same sequence in weight `-1/2`. -/
def heckeMinusHalfWord : List ℕ → (ℤ → ℚ) → (ℤ → ℚ)
  | [], A => A
  | p :: ps, A => heckeMinusHalfWord ps (heckeMinusHalf p A)

/-- The empty weight `-1/2` word is the identity. -/
theorem heckeMinusHalfWord_nil (A : ℤ → ℚ) :
    heckeMinusHalfWord [] A = A := (rfl)

/-- A weight `-1/2` word first applies its head operator. -/
theorem heckeMinusHalfWord_cons (p : ℕ) (ps : List ℕ) (A : ℤ → ℚ) :
    heckeMinusHalfWord (p :: ps) A =
      heckeMinusHalfWord ps (heckeMinusHalf p A) := (rfl)

theorem heckeThreeHalfWord_smul (ps : List ℕ) (c : ℚ) (A : ℤ → ℚ) :
    heckeThreeHalfWord ps (fun r => c * A r) =
      fun r => c * heckeThreeHalfWord ps A r := by
  induction ps generalizing A with
  | nil => rfl
  | cons p ps ih =>
    simp only [heckeThreeHalfWord, heckeThreeHalf_smul, ih]

/-- The squared product is the derivative factor even when primes are repeated. -/
theorem heckeThreeHalfWord_theta (ps : List ℕ) (hps : ∀ p ∈ ps, p ≠ 0)
    (A : ℤ → ℚ) :
    heckeThreeHalfWord ps (thetaCoefficients A) =
      fun r => (ps.prod : ℚ) ^ 2 * thetaCoefficients (heckeMinusHalfWord ps A) r := by
  induction ps generalizing A with
  | nil => simp [heckeThreeHalfWord, heckeMinusHalfWord]
  | cons p ps ih =>
    have hp : p ≠ 0 := hps p (by simp)
    have ht : ∀ q ∈ ps, q ≠ 0 := fun q hq => hps q (by simp [hq])
    rw [heckeThreeHalfWord, heckeThreeHalf_theta hp, heckeThreeHalfWord_smul, ih ht]
    funext r
    simp only [heckeMinusHalfWord, List.prod_cons, Nat.cast_mul, mul_pow]
    ring

end SptClassification.QSeries
