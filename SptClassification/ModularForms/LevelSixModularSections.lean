/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.LevelSixWeierstrass
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.Ring

/-!
# Differential coefficients in the level-six invariant frame

A weight `k` section is written `f(t) ω^k`, where
`ω = dx / (2y + a₁x + a₃)` belongs to the integral Weierstrass family.
The coefficient calculus retains the weight explicitly. In particular,
evaluation of coefficients is not asserted to be a weight-independent
Fourier expansion. The coordinate derivative has poles at the cusps.
-/

public noncomputable section

namespace SptClassification.LevelSixModularSections

open Polynomial

variable {R : Type*} [CommRing R]

/-- Coefficient of the weight-two coordinate derivative in the invariant frame. -/
def coordinateDerivative : R[X] := 12 * X * (X + 8) * (X + 9)

theorem coordinateDerivative_eq :
    (coordinateDerivative : R[X]) = 12 * X * (X + 8) * (X + 9) := (rfl)

/-- Connection coefficient determined by the discriminant and its weight twelve. -/
def connection : R[X] := -(11 * X ^ 2 + 144 * X + 432)

/-- Serre connection on coefficient polynomials of specified weight. -/
def serre (k : ℕ) (f : R[X]) : R[X] :=
  coordinateDerivative * derivative f + C (k : R) * connection * f

@[simp] theorem serre_zero (k : ℕ) : serre k (0 : R[X]) = 0 := by
  simp [serre]

theorem serre_add (k : ℕ) (f g : R[X]) :
    serre k (f + g) = serre k f + serre k g := by
  simp only [serre, derivative_add]
  ring

/-- The weight in the connection term is additive under multiplication. -/
theorem serre_mul (k l : ℕ) (f g : R[X]) :
    serre (k + l) (f * g) = serre k f * g + f * serre l g := by
  simp only [serre, derivative_mul, Nat.cast_add, map_add]
  ring

/-- Scalars do not change the weight of a section. -/
theorem serre_C_mul (k : ℕ) (a : R) (f : R[X]) :
    serre k (C a * f) = C a * serre k f := by
  simp only [serre, derivative_mul, derivative_C, zero_mul, zero_add]
  ring

/-- Evaluations are made in the polynomial coefficient ring, where they exist. -/
theorem eval_serre (k : ℕ) (f : R[X]) (t : R) :
    (serre k f).eval t =
      (12 * t * (t + 8) * (t + 9)) * (derivative f).eval t +
        (k : R) * (-(11 * t ^ 2 + 144 * t + 432)) * f.eval t := by
  simp [serre, coordinateDerivative, connection]

/-- At a zero of a section the connection term disappears. -/
theorem eval_serre_of_eval_eq_zero (k : ℕ) (f : R[X]) (t : R)
    (hf : f.eval t = 0) :
    (serre k f).eval t =
      (12 * t * (t + 8) * (t + 9)) * (derivative f).eval t := by
  rw [eval_serre, hf, mul_zero, add_zero]

/-- The polynomial connection has the usual discriminant normalization. -/
theorem serre_discriminant :
    serre 12 (LevelSixWeierstrass.curve (X : R[X])).Δ = 0 := by
  rw [LevelSixWeierstrass.curve_discriminant]
  simp [serre, coordinateDerivative, connection, derivative_mul, derivative_pow]
  simp only [C_ofNat]
  ring

/-- Ramanujan's weight-four identity in the explicit invariant frame. -/
theorem serre_c₄ :
    3 * serre 4 (LevelSixWeierstrass.curve (X : R[X])).c₄ =
      (LevelSixWeierstrass.curve (X : R[X])).c₆ := by
  rw [LevelSixWeierstrass.curve_c₄]
  simp [serre, coordinateDerivative, connection, derivative_mul, derivative_pow,
    WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  simp only [C_ofNat]
  ring

/-- Ramanujan's weight-six identity, with canonical Tate `c₆ = -E₆`. -/
theorem serre_c₆ :
    2 * serre 6 (LevelSixWeierstrass.curve (X : R[X])).c₆ =
      (LevelSixWeierstrass.curve (X : R[X])).c₄ ^ 2 := by
  simp [serre, coordinateDerivative, connection, derivative_mul, derivative_pow,
    WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  simp only [C_ofNat]
  ring

/-- Regular sections in the invariant frame. The inner variable is the modular
coordinate; the outer variable records powers of the differential. This is a
subring of the sections on the smooth chart, not a global cusp condition. -/
abbrev SectionRing (R : Type*) [CommRing R] := Polynomial (Polynomial R)

/-- A homogeneous section with its weight retained. -/
def sectionOf (k : ℕ) (f : R[X]) : SectionRing R := monomial k f

@[simp] theorem sectionOf_natCast (n : ℕ) :
    sectionOf (R := R) 0 (C (n : R)) = (n : SectionRing R) := by
  simp [sectionOf]

/-- The coordinate derivative is a weight-two section in this frame. -/
def coordinateSection : SectionRing R := sectionOf 2 coordinateDerivative

/-- Homogeneity is an actual coefficient condition in the graded section ring. -/
def IsWeight (k : ℕ) (F : SectionRing R) : Prop := ∃ f, F = sectionOf k f

@[simp] theorem coeff_sectionOf (k : ℕ) (f : R[X]) :
    (sectionOf k f).coeff k = f := by simp [sectionOf]

theorem sectionOf_injective (k : ℕ) : Function.Injective (sectionOf (R := R) k) := by
  intro f g h
  simpa using congrArg (fun F : SectionRing R => F.coeff k) h

theorem sectionOf_add (k : ℕ) (f g : R[X]) :
    sectionOf k (f + g) = sectionOf k f + sectionOf k g := by
  simp [sectionOf, map_add]

theorem sectionOf_mul (k l : ℕ) (f g : R[X]) :
    sectionOf (k + l) (f * g) = sectionOf k f * sectionOf l g := by
  simp [sectionOf, monomial_mul_monomial]

theorem sectionOf_isWeight (k : ℕ) (f : R[X]) : IsWeight k (sectionOf k f) := ⟨f, rfl⟩

/-- Evaluation includes the chosen nonzero differential frame. The map is
also useful with a Laurent-series target at a cusp. -/
def framedEval {S : Type*} [CommRing S] (φ : R →+* S) (t w : S) :
    SectionRing R →+* S := eval₂RingHom (eval₂RingHom φ t) w

theorem framedEval_sectionOf {S : Type*} [CommRing S]
    (φ : R →+* S) (t w : S) (k : ℕ) (f : R[X]) :
    framedEval φ t w (sectionOf k f) = f.eval₂ φ t * w ^ k := by
  simp [framedEval, sectionOf]

/-- The Serre operator on a homogeneous component raises weight by two. -/
def serreSection (k : ℕ) (F : SectionRing R) : SectionRing R :=
  sectionOf (k + 2) (serre k (F.coeff k))

@[simp] theorem serreSection_sectionOf (k : ℕ) (f : R[X]) :
    serreSection k (sectionOf k f) = sectionOf (k + 2) (serre k f) := by
  simp [serreSection]

theorem serreSection_isWeight (k : ℕ) (F : SectionRing R) :
    IsWeight (k + 2) (serreSection k F) := ⟨_, rfl⟩

theorem serreSection_leibniz (k l : ℕ) (F G : SectionRing R)
    (hF : IsWeight k F) (hG : IsWeight l G) :
    serreSection (k + l) (F * G) = serreSection k F * G + F * serreSection l G := by
  obtain ⟨f, rfl⟩ := hF
  obtain ⟨g, rfl⟩ := hG
  rw [← sectionOf_mul, serreSection_sectionOf, serre_mul, sectionOf_add,
    serreSection_sectionOf, serreSection_sectionOf, ← sectionOf_mul, ← sectionOf_mul]
  congr 2 <;> omega

variable {K : Type*} [Field K]

/-- The coordinate coefficient is nonzero at every interior point. -/
theorem coordinateDerivative_eval_ne_zero (t : K) (h6 : (6 : K) ≠ 0)
    (ht : t ≠ 0) (h8 : t ≠ -8) (h9 : t ≠ -9) :
    (coordinateDerivative : K[X]).eval t ≠ 0 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    apply h6
    calc (6 : K) = 2 * 3 := by norm_num
         _ = 0 := by rw [h, zero_mul]
  have h12 : (12 : K) ≠ 0 := by
    have : (12 : K) = 2 * 6 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h6
  simpa [coordinateDerivative, add_eq_zero_iff_eq_neg] using
    mul_ne_zero (mul_ne_zero (mul_ne_zero h12 ht)
      (show t + 8 ≠ 0 from by simpa [add_eq_zero_iff_eq_neg] using h8))
      (show t + 9 ≠ 0 from by simpa [add_eq_zero_iff_eq_neg] using h9)

/-- The coordinate derivative stays nonzero in every nonzero frame. -/
theorem framedEval_coordinateSection_ne_zero (t w : K) (hw : w ≠ 0)
    (h6 : (6 : K) ≠ 0) (ht : t ≠ 0) (h8 : t ≠ -8) (h9 : t ≠ -9) :
    framedEval (RingHom.id K) t w coordinateSection ≠ 0 := by
  rw [coordinateSection, framedEval_sectionOf]
  simpa using mul_ne_zero
    (coordinateDerivative_eval_ne_zero t h6 ht h8 h9) (pow_ne_zero 2 hw)

/-- Simple interior zeros remain nonzero after the Serre derivative. -/
theorem eval_serre_ne_zero_of_simple_zero (k : ℕ) (f : K[X]) (t : K)
    (h6 : (6 : K) ≠ 0) (ht : t ≠ 0) (h8 : t ≠ -8) (h9 : t ≠ -9)
    (hf : f.eval t = 0) (hf' : (derivative f).eval t ≠ 0) :
    (serre k f).eval t ≠ 0 := by
  rw [eval_serre_of_eval_eq_zero k f t hf]
  apply mul_ne_zero _ hf'
  simpa [coordinateDerivative] using coordinateDerivative_eval_ne_zero t h6 ht h8 h9

end SptClassification.LevelSixModularSections
