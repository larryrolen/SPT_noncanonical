/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaWeaklyHolomorphic
public import SptClassification.ModularForms.PrincipalPartHolomorphy
public import SptClassification.ModularForms.PrincipalPartDerivativeCusp

/-!
# The eta polynomial families as actual weakly holomorphic forms

The verified analytic transformation laws, holomorphy, and meromorphic cusp
representatives construct the two weak-form families used in
[rolenManuscript, §3]. Fourier integrality is proved separately.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- Every integral eta polynomial is a weakly holomorphic form of weight `1/2`. -/
noncomputable def etaJWeakForm (P : Polynomial ℤ) : EtaWeaklyHolomorphicForm 0 where
  toFun := etaJPolynomial P
  holomorphic' := etaJPolynomial_mdifferentiable P
  map_action' γ hγ τ := by
    apply mul_right_cancel₀ (ModularForm.eta_ne_zero τ.im_pos)
    calc
      _ = ModularForm.eta (γ • τ : UpperHalfPlane) * etaJPolynomial P τ :=
        etaJPolynomial_cross_transform P γ hγ τ
      _ = _ := by
        rw [← etaAutomorphyFactor_mul_eta γ τ]
        ring
  meromorphic_cusp' := etaJPolynomial_has_meromorphic_cusp P

/-- Every derivative eta polynomial is a weakly holomorphic form of weight `5/2`. -/
noncomputable def etaThetaJWeakForm (P : Polynomial ℤ) : EtaWeaklyHolomorphicForm 2 where
  toFun := etaThetaJPolynomial P
  holomorphic' := etaThetaJPolynomial_mdifferentiable P
  map_action' γ hγ τ := by
    apply mul_right_cancel₀ (ModularForm.eta_ne_zero τ.im_pos)
    calc
      _ = ModularForm.eta (γ • τ : UpperHalfPlane) * denom γ τ ^ 2 *
          etaThetaJPolynomial P τ := etaThetaJPolynomial_cross_transform P γ hγ τ
      _ = _ := by
        rw [← etaAutomorphyFactor_mul_eta γ τ]
        ring
  meromorphic_cusp' := etaThetaJPolynomial_has_meromorphic_cusp P

/-- Evaluation of the bundled eta polynomial is its original analytic function. -/
@[simp] theorem etaJWeakForm_apply (P : Polynomial ℤ) (τ : UpperHalfPlane) :
    etaJWeakForm P τ = etaJPolynomial P τ := (rfl)

/-- Evaluation of the bundled derivative polynomial is its original analytic function. -/
@[simp] theorem etaThetaJWeakForm_apply (P : Polynomial ℤ) (τ : UpperHalfPlane) :
    etaThetaJWeakForm P τ = etaThetaJPolynomial P τ := (rfl)

end SptClassification
