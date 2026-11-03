/- Assembled by AxiomProver. -/

module

public import SptClassification.QuadraticForms.TraceGramGeometry
public import SptClassification.QuadraticForms.ConditionalSeparation

/-!
# CM separation from a positive trace realization

The real trace pairing in [rolen2026canonical, Lemma 5.2] supplies the
Hadamard bound through its Euclidean realization. The remaining CM descent,
orientation and Eichler laws are stated for the actual oriented class
polynomials as explicit geometric inputs.
-/

public section

open scoped RealInnerProductSpace

namespace SptClassification
namespace ConditionalCM

/-- Data from a common root of the two reduced CM models, with a positive
real realization of the trace pairing in place of an assumed determinant
inequality. The restriction map belongs to the integral preserving order. -/
structure RealizedCommonRootAction (d p : ℕ) where
  O : Type
  D : Type
  H : Type
  [ringO : Ring O]
  [divisionD : DivisionRing D]
  [divisionH : DivisionRing H]
  order : PreservingOrder O D
  intoReal : D →+* H
  intoReal_injective : Function.Injective intoReal
  scalar : ℝ →+* H
  scalar_injective : Function.Injective scalar
  scalar_central : ∀ (r : ℝ) (x : H), scalar r * x = x * scalar r
  alpha : O
  beta : O
  normNumber : ℕ
  normNumber_eq : 4 * normNumber = d + 1
  alpha_quadratic : order.intoDivision alpha * order.intoDivision alpha -
    order.intoDivision alpha + (normNumber : D) = 0
  beta_quadratic : order.intoDivision beta * order.intoDivision beta -
    order.intoDivision beta + (normNumber : D) = 0
  alpha_orientation : order.restriction alpha = 0 ∨ order.restriction alpha = 1
  beta_orientation : order.restriction beta = 3 ∨ order.restriction beta = 4
  ordinary : Prop
  ordinary_commutes : ordinary → ∀ x y : O,
    order.intoDivision x * order.intoDivision y =
      order.intoDivision y * order.intoDivision x
  reducedTrace : H → ℝ
  quaternionConj : H → H
  reducedNorm : H → ℝ
  trace_self : ∀ x : H, reducedTrace (x * quaternionConj x) = 2 * reducedNorm x
  norm_one : reducedNorm 1 = 1
  norm_mul : ∀ x y : H, reducedNorm (x * y) = reducedNorm x * reducedNorm y
  norm_alpha : reducedNorm (intoReal (order.intoDivision alpha)) = (normNumber : ℝ)
  norm_beta : reducedNorm (intoReal (order.intoDivision beta)) = (normNumber : ℝ)
  rho : H → EuclideanSpace ℝ (Fin 4)
  rho_trace : ∀ x y : H, inner ℝ (rho x) (rho y) = reducedTrace (x * quaternionConj y)
  eichler_lower : ¬ordinary → ∀ v : Fin 4 → O,
    (∀ c : Fin 4 → ℝ,
      (∑ i : Fin 4, scalar (c i) * intoReal (order.intoDivision (v i))) = 0 →
        ∀ i, c i = 0) →
    6 * (p : ℝ) ≤ traceCovolume reducedTrace quaternionConj
      (fun i => intoReal (order.intoDivision (v i)))

/-- The old conditional action is obtained by proving its universal
Hadamard field from the positive trace realization. -/
def RealizedCommonRootAction.toCommonRootAction {d p : ℕ}
    (R : RealizedCommonRootAction d p) : CommonRootAction d p where
  O := R.O
  D := R.D
  H := R.H
  ringO := R.ringO
  divisionD := R.divisionD
  divisionH := R.divisionH
  order := R.order
  intoReal := R.intoReal
  intoReal_injective := R.intoReal_injective
  scalar := R.scalar
  scalar_injective := R.scalar_injective
  scalar_central := R.scalar_central
  alpha := R.alpha
  beta := R.beta
  normNumber := R.normNumber
  normNumber_eq := R.normNumber_eq
  alpha_quadratic := R.alpha_quadratic
  beta_quadratic := R.beta_quadratic
  alpha_orientation := R.alpha_orientation
  beta_orientation := R.beta_orientation
  ordinary := R.ordinary
  ordinary_commutes := R.ordinary_commutes
  reducedTrace := R.reducedTrace
  quaternionConj := R.quaternionConj
  reducedNorm := R.reducedNorm
  trace_self := R.trace_self
  norm_one := R.norm_one
  norm_mul := R.norm_mul
  norm_alpha := R.norm_alpha
  norm_beta := R.norm_beta
  hadamard := @trace_covolume_le_of_realization R.H R.divisionH R.reducedTrace
    R.quaternionConj R.rho R.rho_trace
  eichler_lower := R.eichler_lower

/-- A common root under realized trace geometry forces the reverse of the
strict numerical separation bound. -/
theorem RealizedCommonRootAction.bound {d p : ℕ}
    (R : RealizedCommonRootAction d p) (hd : 0 < d) :
    24 * (p : ℝ) ≤ ((d : ℝ) + 1) ^ 2 :=
  R.toCommonRootAction.bound hd

/-- Localized integral models of the actual oriented class polynomials.
A common root supplies real trace geometry, rather than a prepackaged
Hadamard inequality. -/
structure RealizedCMDescentInput (d p : ℕ)
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime] where
  modelA : Polynomial (Localization.Away (6 : ℤ))
  modelB : Polynomial (Localization.Away (6 : ℤ))
  modelA_monic : modelA.Monic
  modelB_monic : modelB.Monic
  complexSpecialization : Localization.Away (6 : ℤ) →+* ℂ
  complexA : modelA.map complexSpecialization = cmClassPolynomialA (-(d : ℤ))
  complexB : modelB.map complexSpecialization = cmClassPolynomialB (-(d : ℤ))
  reduction : Localization.Away (6 : ℤ) →+* ZMod p
  commonRoot : ∀ x : AlgebraicClosure (ZMod p),
    (Polynomial.aeval x) (modelA.map reduction) = 0 →
    (Polynomial.aeval x) (modelB.map reduction) = 0 →
    RealizedCommonRootAction d p

/-- Forget the additional real trace realization after proving its
universal determinant bound. The actual integral models are unchanged. -/
def RealizedCMDescentInput.toCMDescentInput {d p : ℕ}
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (I : RealizedCMDescentInput d p) : CMDescentInput d p where
  modelA := I.modelA
  modelB := I.modelB
  modelA_monic := I.modelA_monic
  modelB_monic := I.modelB_monic
  complexSpecialization := I.complexSpecialization
  complexA := I.complexA
  complexB := I.complexB
  reduction := I.reduction
  commonRoot := fun x ha hb => (I.commonRoot x ha hb).toCommonRootAction

/-- Separation for the reductions of the actual CM class polynomials,
conditional on localized descent, CM/Eichler geometry and the positive
realization of reduced trace. The Hadamard bound is proved here. -/
theorem cm_separation_of_realization (d p : ℕ)
    [Fact (-(d : ℤ) < 0)] [Fact p.Prime]
    (hd : 0 < d) (hsq : Squarefree d) (hmod : d % 24 = 23)
    (hp : 5 ≤ p) (hcop : ¬p ∣ 6 * d)
    (hbound : (d + 1) ^ 2 < 24 * p)
    (I : RealizedCMDescentInput d p) :
    IsCoprime (I.modelA.map I.reduction) (I.modelB.map I.reduction) := by
  exact conditional_cm_separation d p hd hsq hmod hp hcop hbound I.toCMDescentInput

end ConditionalCM
end SptClassification
