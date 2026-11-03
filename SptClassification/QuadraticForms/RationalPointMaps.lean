/- Assembled by AxiomProver. -/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Set.Finite.Basic

/-!
# Rational coordinates compatible with elliptic point maps

The coordinates below describe the supplied point map itself. In particular,
an unrelated function-field map cannot certify its algebraicity. The rational
description is required away from a finite exceptional set of geometric points.
The zero homomorphism is included separately, since its image is at infinity.

This is coordinate data, not an endomorphism-specialization theorem. Extending
the rational map to a morphism uses nonsingularity and projectivity; constructing
such data for lattice multiplication is a separate classical input.
-/

public section

namespace SptClassification

/-- Additive homomorphisms on an infinite group are determined outside any
finite exceptional set. This also identifies the action at exceptional points
after an additive rational map has been extended. -/
theorem addHom_eq_of_eq_off_finite
    {G H : Type*} [AddCommGroup G] [Infinite G] [AddGroup H]
    (f g : G →+ H) (S : Set G) (hS : S.Finite)
    (h : ∀ x ∉ S, f x = g x) : f = g := by
  ext x
  obtain ⟨y, hy⟩ := (hS.union (hS.image (fun z => -x + z))).exists_notMem
  have hyS : y ∉ S := fun hmem => hy (Or.inl hmem)
  have hxyS : x + y ∉ S := by
    intro hmem
    apply hy
    exact Or.inr ⟨x + y, hmem, by simp⟩
  have heq := h (x + y) hxyS
  rw [map_add, map_add, h y hyS] at heq
  exact add_right_cancel heq

namespace RationalPointMap

/-- Two fractions in the affine coordinates `x,y`. -/
structure Coordinates (F : Type*) [CommRing F] where
  numeratorX : MvPolynomial (Fin 2) F
  denominatorX : MvPolynomial (Fin 2) F
  numeratorY : MvPolynomial (Fin 2) F
  denominatorY : MvPolynomial (Fin 2) F

/-- Evaluation with variable zero equal to `x` and variable one equal to `y`. -/
noncomputable def evaluate {F : Type*} [CommRing F]
    (p : MvPolynomial (Fin 2) F) (x y : F) : F :=
  MvPolynomial.eval (fun i => if i = 0 then x else y) p

/-- The two fractions represent the given point map outside `S`.
Denominators are required to be nonzero at every point where the formula
is asserted, and the output coordinates satisfy the actual curve equation. -/
def Coordinates.Represents {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve.Affine F} (r : Coordinates F)
    (f : W₁.Point → W₂.Point) (S : Set W₁.Point) : Prop :=
  ∀ (x y : F) (h : W₁.Nonsingular x y),
    WeierstrassCurve.Affine.Point.some x y h ∉ S →
      ∃ (u v : F) (huv : W₂.Nonsingular u v),
        f (.some x y h) = .some u v huv ∧
        evaluate r.denominatorX x y ≠ 0 ∧
        evaluate r.denominatorY x y ≠ 0 ∧
        u * evaluate r.denominatorX x y = evaluate r.numeratorX x y ∧
        v * evaluate r.denominatorY x y = evaluate r.numeratorY x y

/-- A homomorphism described by rational affine coordinates, or the zero map.
The infinitude requirement prevents a vacuous certificate obtained by placing
all rational points of a finite field in the exceptional set. Applications to
algebraic endomorphisms use geometric points over an algebraically closed field. -/
def IsRational {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve.Affine F}
    (f : W₁.Point →+ W₂.Point) : Prop :=
  Infinite W₁.Point ∧
    (f = 0 ∨ ∃ (r : Coordinates F) (S : Set W₁.Point),
      S.Finite ∧ r.Represents f S)

/-- Two additive point maps represented by the same rational coordinates
agree everywhere, including at poles and at infinity. -/
theorem eq_of_represents {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve.Affine F} [Infinite W₁.Point]
    (f g : W₁.Point →+ W₂.Point) (r : Coordinates F)
    (S T : Set W₁.Point) (hS : S.Finite) (hT : T.Finite)
    (hf : r.Represents f S) (hg : r.Represents g T) : f = g := by
  apply addHom_eq_of_eq_off_finite f g (S ∪ T) (hS.union hT)
  intro P hP
  cases P with
  | zero => exact (map_zero f).trans (map_zero g).symm
  | some x y h =>
    obtain ⟨u, v, huv, heqf, hx, hy, hux, hvy⟩ :=
      hf x y h (fun hmem => hP (Or.inl hmem))
    obtain ⟨u', v', huv', heqg, _, _, hux', hvy'⟩ :=
      hg x y h (fun hmem => hP (Or.inr hmem))
    have hu : u = u' := mul_right_cancel₀ hx (hux.trans hux'.symm)
    have hv : v = v' := mul_right_cancel₀ hy (hvy.trans hvy'.symm)
    subst u'
    subst v'
    exact heqf.trans heqg.symm

end RationalPointMap
end SptClassification
