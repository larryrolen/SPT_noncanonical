/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartPolynomial
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold

/-!
# Derivatives of the level-one invariant

Differentiating the invariant supplies the weight-two factor in the
weight-five-halves principal-part family [rolenManuscript, §3].
These transformation laws do not assert meromorphy at the cusp.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups Manifold

/-- Differentiating level-one invariance gives a weight-two transformation. -/
theorem levelOneJ_deriv_transform (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ)
    (τ : UpperHalfPlane) :
    deriv (levelOneJ ∘ ofComplex) (γ • τ : UpperHalfPlane) =
      denom γ τ ^ 2 * deriv (levelOneJ ∘ ofComplex) τ := by
  have hdet : γ.val.det = 1 := by
    simpa using congrArg Units.val (Subgroup.HasDetOne.det_eq hγ)
  have hpos : 0 < γ.val.det := by rw [hdet]; norm_num
  have hτ := (mdifferentiableAt_iff.mp (levelOneJ_mdifferentiable τ)).hasDerivAt
  have hγτ :=
    (mdifferentiableAt_iff.mp (levelOneJ_mdifferentiable (γ • τ))).hasDerivAt
  have haction := (hasStrictDerivAt_smul hpos τ).hasDerivAt
  rw [hdet] at haction
  have hchain : HasDerivAt (levelOneJ ∘ ofComplex)
      (deriv (levelOneJ ∘ ofComplex) (γ • τ : UpperHalfPlane) *
        (1 / denom γ τ ^ 2)) (τ : ℂ) := by
    convert hγτ.comp_of_eq (τ : ℂ) haction (by simp) using 1
    simp only [Function.comp_def, ofComplex_apply, levelOneJ_invariant γ hγ]
  have heq := hchain.unique hτ
  have hmul := (div_eq_iff (pow_ne_zero 2 (denom_ne_zero γ τ))).mp
    (show deriv (levelOneJ ∘ ofComplex) (γ • τ : UpperHalfPlane) /
      denom γ τ ^ 2 = deriv (levelOneJ ∘ ofComplex) τ by
        simpa only [div_eq_mul_inv, one_mul] using heq)
  simpa only [mul_comm] using hmul

/-- The normalized complex derivative `Θj = (2πi)⁻¹ j'`. -/
noncomputable def thetaLevelOneJ (τ : UpperHalfPlane) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * deriv (levelOneJ ∘ ofComplex) τ

/-- The complex-chart derivative formula for the normalized invariant. -/
theorem thetaLevelOneJ_eq (τ : UpperHalfPlane) :
    thetaLevelOneJ τ =
      (2 * Real.pi * Complex.I)⁻¹ * deriv (levelOneJ ∘ ofComplex) τ :=
  (rfl)

theorem thetaLevelOneJ_transform (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ)
    (τ : UpperHalfPlane) :
    thetaLevelOneJ (γ • τ) = denom γ τ ^ 2 * thetaLevelOneJ τ := by
  simp only [thetaLevelOneJ, levelOneJ_deriv_transform γ hγ]
  ring

/-- The analytic derivative polynomial family used to construct `K_d`. -/
noncomputable def etaThetaJPolynomial (P : Polynomial ℤ) (τ : UpperHalfPlane) : ℂ :=
  -ModularForm.eta τ * thetaLevelOneJ τ * (P.map (Int.castRingHom ℂ)).eval (levelOneJ τ)

/-- The analytic evaluation formula for a derivative eta polynomial. -/
theorem etaThetaJPolynomial_eq (P : Polynomial ℤ) (τ : UpperHalfPlane) :
    etaThetaJPolynomial P τ =
      -ModularForm.eta τ * thetaLevelOneJ τ *
        (P.map (Int.castRingHom ℂ)).eval (levelOneJ τ) :=
  (rfl)

/-- The derivative family has eta's automorphy factor times the weight-two factor. -/
theorem etaThetaJPolynomial_cross_transform (P : Polynomial ℤ)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (τ : UpperHalfPlane) :
    etaThetaJPolynomial P (γ • τ) * ModularForm.eta τ =
      ModularForm.eta ((γ • τ : UpperHalfPlane) : ℂ) *
        denom γ τ ^ 2 * etaThetaJPolynomial P τ := by
  simp only [etaThetaJPolynomial, thetaLevelOneJ_transform γ hγ,
    levelOneJ_invariant γ hγ]
  ring

end SptClassification
