/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartDerivative
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Algebra.Polynomial.Inductions

/-!
# Holomorphy of the principal-part polynomial families

The analytic invariant and its normalized derivative are holomorphic on the
upper half-plane. Consequently both polynomial families used for `H_d` and `K_d`
are holomorphic there [rolenManuscript, §3]. Cusp meromorphy and Fourier
coefficient identification are separate assertions.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold Topology

/-- The invariant's complex chart is analytic at each upper-half-plane point. -/
theorem analyticAt_levelOneJ_chart (τ : UpperHalfPlane) :
    AnalyticAt ℂ (levelOneJ ∘ ofComplex) (τ : ℂ) := by
  exact (UpperHalfPlane.mdifferentiable_iff.mp levelOneJ_mdifferentiable).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)

/-- The normalized derivative of the invariant is holomorphic. -/
theorem thetaLevelOneJ_mdifferentiable : MDiff thetaLevelOneJ := by
  intro τ
  apply mdifferentiableAt_iff.mpr
  have hd : DifferentiableAt ℂ
      (fun z : ℂ => (2 * Real.pi * Complex.I)⁻¹ * deriv (levelOneJ ∘ ofComplex) z)
      (τ : ℂ) :=
    (analyticAt_const.mul (analyticAt_levelOneJ_chart τ).deriv).differentiableAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  simpa only [Function.comp_apply, thetaLevelOneJ_eq, id_eq] using
    congrArg (fun w : ℂ => (2 * Real.pi * Complex.I)⁻¹ *
      deriv (levelOneJ ∘ ofComplex) w) hz

private theorem eta_mdifferentiable : MDiff (fun τ : UpperHalfPlane => ModularForm.eta τ) := by
  intro τ
  apply mdifferentiableAt_iff.mpr
  apply (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet τ.im_pos).congr_of_eventuallyEq
  filter_upwards [eventuallyEq_coe_comp_ofComplex τ.im_pos] with z hz
  exact congrArg ModularForm.eta hz

private theorem mdifferentiable_polynomial_eval (P : Polynomial ℂ)
    {f : UpperHalfPlane → ℂ} (hf : MDiff f) :
    MDiff (fun τ => P.eval (f τ)) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      funext τ
      exact Polynomial.eval_add
  | monomial n a =>
      convert (mdifferentiable_const.mul (hf.pow n) :
        MDiff ((fun _ : UpperHalfPlane => a) * (fun τ => f τ ^ n))) using 1
      funext τ
      exact Polynomial.eval_monomial

/-- Holomorphy of every eta polynomial in the invariant. -/
theorem etaJPolynomial_mdifferentiable (P : Polynomial ℤ) : MDiff (etaJPolynomial P) := by
  have hfun : etaJPolynomial P = fun τ : UpperHalfPlane =>
      ModularForm.eta τ * (P.map (Int.castRingHom ℂ)).eval (levelOneJ τ) :=
    funext (etaJPolynomial_eq P)
  rw [hfun]
  exact eta_mdifferentiable.mul (mdifferentiable_polynomial_eval
    (P.map (Int.castRingHom ℂ)) levelOneJ_mdifferentiable)

/-- Holomorphy of every derivative eta polynomial in the invariant. -/
theorem etaThetaJPolynomial_mdifferentiable (P : Polynomial ℤ) :
    MDiff (etaThetaJPolynomial P) := by
  have hfun : etaThetaJPolynomial P = fun τ : UpperHalfPlane =>
      -ModularForm.eta τ * thetaLevelOneJ τ *
        (P.map (Int.castRingHom ℂ)).eval (levelOneJ τ) :=
    funext (etaThetaJPolynomial_eq P)
  rw [hfun]
  exact (eta_mdifferentiable.neg.mul thetaLevelOneJ_mdifferentiable).mul
    (mdifferentiable_polynomial_eval
      (P.map (Int.castRingHom ℂ)) levelOneJ_mdifferentiable)

end SptClassification
