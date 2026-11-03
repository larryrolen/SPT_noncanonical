/- Assembled by AxiomProver. -/

module

public import SptClassification.EllipticCurves.PolynomialCartier
public import SptClassification.EllipticCurves.DeuringPolynomialReduction
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Polynomial Cartier calculation for the Legendre cubic

For the Legendre equation `Y² = X(X-1)(X-λ)`, the polynomial multiplying
`dX/Y^p` in `dX/Y` is the `((p-1)/2)`-th power of the cubic. Its Cartier
image is constant, with coefficient given by the Deuring polynomial.
The passage from this calculation to Cartier on the curve's function field
requires the differential relation on that field. See [silverman2009,
Chapter V].
-/

public section

namespace SptClassification

open Polynomial

/-- The Legendre cubic has polynomial degree at most three. -/
theorem natDegree_legendreCubic_le {k : Type*} [Field k] (lam : k) :
    (X * (X - 1) * (X - C lam) : k[X]).natDegree ≤ 3 := by
  have h₁ : (X - 1 : k[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have h₂ : (X - C lam : k[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  have h₃ : (X * (X - 1) : k[X]).natDegree ≤
      (X : k[X]).natDegree + (X - 1 : k[X]).natDegree := natDegree_mul_le
  have h₄ : (X * (X - 1) * (X - C lam) : k[X]).natDegree ≤
      (X * (X - 1) : k[X]).natDegree + (X - C lam : k[X]).natDegree :=
    natDegree_mul_le
  simp only [natDegree_X] at h₃
  omega

/-- Powers of the Legendre cubic obey the expected elementary degree bound. -/
theorem natDegree_legendreCubic_pow_le {k : Type*} [Field k]
    (lam : k) (n : ℕ) :
    ((X * (X - 1) * (X - C lam)) ^ n : k[X]).natDegree ≤ 3 * n := by
  let f : k[X] := X * (X - 1) * (X - C lam)
  have hf : f.natDegree ≤ 3 := natDegree_legendreCubic_le lam
  change (f ^ n).natDegree ≤ 3 * n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hmul : ((f ^ n) * f).natDegree ≤
          (f ^ n).natDegree + f.natDegree := natDegree_mul_le
      omega

/-- The polynomial coefficient appearing in the Cartier calculation is
`(-1)^n D_n(λ)`, with `n=(p-1)/2`. -/
theorem polynomialCartier_legendreCubic_pow {k : Type*} [Field k]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP k p]
    (hp : 5 ≤ p) (hperfect : Function.Bijective (frobenius k p)) (lam : k) :
    let n := (p - 1) / 2
    polynomialCartier p (perfectFrobeniusEquiv p hperfect)
        ((X * (X - 1) * (X - C lam)) ^ n : k[X]) =
      C ((perfectFrobeniusEquiv p hperfect).symm
        ((-1 : k) ^ n * (deuringPolynomialIn k n).eval lam)) := by
  dsimp
  let n := (p - 1) / 2
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two (by omega)
  have hn : 2 * n = p - 1 := by
    obtain ⟨m, hm⟩ := hodd
    dsimp [n]
    omega
  have hdegree :
      ((X * (X - 1) * (X - C lam)) ^ n : k[X]).natDegree < 2 * p - 1 := by
    have hbound := natDegree_legendreCubic_pow_le lam n
    omega
  rw [polynomialCartier_eq_C_of_natDegree_lt p (by omega) _ _ hdegree]
  have hcoeff :
      ((X * (X - 1) * (X - C lam)) ^ n : k[X]).coeff (p - 1) =
        (-1 : k) ^ n * (deuringPolynomialIn k n).eval lam := by
    rw [← hn]
    exact coeff_legendreCubic_pow k n lam
  rw [hcoeff]

/-- On the Legendre curve, the equation `y² = x(x-1)(x-λ)` rewrites
`y^p` as `y` times the `((p-1)/2)`-th power of the cubic. This identity
is the algebraic input to the Cartier calculation for `dx/y`. -/
theorem legendre_y_pow_odd {R : Type*} [CommRing R]
    (p : ℕ) (hodd : Odd p) (x y lam : R)
    (hcurve : y ^ 2 = x * (x - 1) * (x - lam)) :
    y ^ p = y * (x * (x - 1) * (x - lam)) ^ ((p - 1) / 2) := by
  obtain ⟨m, hm⟩ := hodd
  have hn : 2 * ((p - 1) / 2) = p - 1 := by omega
  have hp : p = 2 * ((p - 1) / 2) + 1 := by omega
  calc
    y ^ p = y ^ (2 * ((p - 1) / 2) + 1) := congrArg (y ^ ·) hp
    _ = (y ^ 2) ^ ((p - 1) / 2) * y := by rw [pow_add, pow_mul, pow_one]
    _ = y * (x * (x - 1) * (x - lam)) ^ ((p - 1) / 2) := by rw [hcurve]; ring

end SptClassification
