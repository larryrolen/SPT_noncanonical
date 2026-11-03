/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic.Ring

/-!
# Hasse coefficients of Weierstrass equations

The integral cubic is `(2y+a₁x+a₃)² = 4x³+b₂x²+2b₄x+b₆`.
In odd characteristic `p`, its indicated coefficient is the Hasse invariant
in the frame `dx/(2y+a₁x+a₃)`: the apparent normalization factor is
`2^(p-1)=1`. The literature interfaces below concern arbitrary Weierstrass
families, independently of the manuscript's CM forms.
-/

public noncomputable section

namespace SptClassification.WeierstrassHasse

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The cubic obtained by completing the square integrally. -/
def cubic (W : WeierstrassCurve R) : R[X] :=
  4 * X ^ 3 + C W.b₂ * X ^ 2 + 2 * C W.b₄ * X + C W.b₆

/-- Hasse coefficient in the invariant differential frame, in odd characteristic. -/
def hasse (p : ℕ) (W : WeierstrassCurve R) : R :=
  ((cubic W) ^ ((p - 1) / 2)).coeff (p - 1)

/-- The coefficient construction commutes with every base change. -/
theorem map_hasse (p : ℕ) (W : WeierstrassCurve R) (φ : R →+* S) :
    φ (hasse p W) = hasse p (W.map φ) := by
  simp only [hasse, ← coeff_map, ← Polynomial.map_pow]
  congr 2
  simp [cubic, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  simp only [map_ofNat]

/-- Numerator of the Kodaira–Spencer coefficient of a Weierstrass family.
It detects transversality even over the fibers with `j = 0` or `1728`. -/
def ksNumerator (W : WeierstrassCurve R[X]) : R[X] :=
  2 * W.c₄ * derivative W.c₆ - 3 * W.c₆ * derivative W.c₄

theorem ksNumerator_eq (W : WeierstrassCurve R[X]) :
    ksNumerator W = 2 * W.c₄ * derivative W.c₆ - 3 * W.c₆ * derivative W.c₄ := (rfl)

/-- Coefficients at infinity after changing frame by `t`, for weights `1,2,3,4,6`. -/
def infinityFiber (W : WeierstrassCurve R[X]) : WeierstrassCurve R where
  a₁ := W.a₁.coeff 1
  a₂ := W.a₂.coeff 2
  a₃ := W.a₃.coeff 3
  a₄ := W.a₄.coeff 4
  a₆ := W.a₆.coeff 6

@[simp] theorem infinityFiber_a₁ (W : WeierstrassCurve R[X]) :
    (infinityFiber W).a₁ = W.a₁.coeff 1 := (rfl)
@[simp] theorem infinityFiber_a₂ (W : WeierstrassCurve R[X]) :
    (infinityFiber W).a₂ = W.a₂.coeff 2 := (rfl)
@[simp] theorem infinityFiber_a₃ (W : WeierstrassCurve R[X]) :
    (infinityFiber W).a₃ = W.a₃.coeff 3 := (rfl)
@[simp] theorem infinityFiber_a₄ (W : WeierstrassCurve R[X]) :
    (infinityFiber W).a₄ = W.a₄.coeff 4 := (rfl)
@[simp] theorem infinityFiber_a₆ (W : WeierstrassCurve R[X]) :
    (infinityFiber W).a₆ = W.a₆.coeff 6 := (rfl)

/-- The five coefficient bounds that extend a Weierstrass equation over `P¹`
with invariant differential bundle `O(1)`. -/
def HasWeightBounds (W : WeierstrassCurve R[X]) : Prop :=
  W.a₁.natDegree ≤ 1 ∧ W.a₂.natDegree ≤ 2 ∧ W.a₃.natDegree ≤ 3 ∧
    W.a₄.natDegree ≤ 4 ∧ W.a₆.natDegree ≤ 6

theorem hasWeightBounds_iff (W : WeierstrassCurve R[X]) :
    HasWeightBounds W ↔ W.a₁.natDegree ≤ 1 ∧ W.a₂.natDegree ≤ 2 ∧
      W.a₃.natDegree ≤ 3 ∧ W.a₄.natDegree ≤ 4 ∧ W.a₆.natDegree ≤ 6 := Iff.rfl

/-- Weight homogeneity of the classical Hasse coefficient, in a polynomial
Weierstrass family. [katz1973], §2.0, pp. 97–98 (weight `p-1`), and Appendix
A1.4, Remark 2, p. 172 (coefficient formula). The frame changes by `t` at
infinity; hence the coefficient polynomial has degree at most `p-1`. -/
theorem hasse_degree_bound_literature (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve R[X]) (hW : HasWeightBounds W) (hp : 2 < p) :
    (hasse p W).natDegree ≤ p - 1 := by
  sorry

/-- The same weight homogeneity identifies the top coefficient with the Hasse
coefficient of the fiber in the infinity frame. [katz1973], §2.0, pp. 97–98,
and Appendix A1.4, Remark 2, p. 172. This is an identity of coefficients,
not a statement that this particular family is a modular curve. -/
theorem hasse_top_coefficient_literature (p : ℕ) [Fact p.Prime]
    (W : WeierstrassCurve R[X]) (hW : HasWeightBounds W) (hp : 2 < p) :
    (hasse p W).coeff (p - 1) = hasse p (infinityFiber W) := by
  sorry

/-- Covariance of the actual Hasse coefficient under a Weierstrass coordinate
change. [katz1973], §2.0, pp. 97–98 (weight), and A1.4, Remark 2, p. 172
(coefficient formula). Mathlib's action divides the coefficient of weight `i`
by `C.u^i`; the inverse power here retains that convention. -/
theorem hasse_variableChange_literature (p : ℕ) [Fact p.Prime] [CharP R p]
    (hp : 3 < p) (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    hasse p (C • W) = (↑C.u⁻¹ : R) ^ (p - 1) * hasse p W := by
  sorry

variable {K : Type*} [Field K]

/-- Multiplicative fibers have nonzero Hasse invariant. This includes singular
nodal Weierstrass fibers. [katz1973], §2.0, pp. 97–98: the Hasse invariant on
the Tate curve is `1`, including its multiplicative special fiber. The
nonvanishing is independent of the chosen invariant differential frame. -/
theorem hasse_ne_zero_of_multiplicative_literature (p : ℕ) [Fact p.Prime]
    [CharP K p] (hp : 3 < p) (W : WeierstrassCurve K)
    (hΔ : W.Δ = 0) (hc : W.c₄ ≠ 0) : hasse p W ≠ 0 := by
  sorry

/-- Igusa's simple-zero theorem pulled back along a transverse Weierstrass
family. [katz1973], proof of Theorem 4.3, p. 149 (the completed deformation
ring is `k[[A]]`), and Appendix A1.3.17, p. 169 (Kodaira–Spencer detects an
étale classifying map). The coefficient numerator is the usual invariant
expression for this map; characteristic two and three are excluded. No
restriction excluding the elliptic `j` values is imposed. -/
theorem hasse_simple_zero_of_transverse_literature (p : ℕ) [Fact p.Prime]
    [CharP K p] [IsAlgClosed K] (hp : 3 < p) (W : WeierstrassCurve K[X]) (t : K)
    (hΔ : W.Δ.eval t ≠ 0) (hKS : (ksNumerator W).eval t ≠ 0)
    (hH : (hasse p W).eval t = 0) :
    (derivative (hasse p W)).eval t ≠ 0 := by
  sorry

end SptClassification.WeierstrassHasse
