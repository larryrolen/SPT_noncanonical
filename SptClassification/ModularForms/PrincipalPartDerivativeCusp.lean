/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartCusp
public import SptClassification.ModularForms.PrincipalPartDerivative

/-!
# Cusp representations of the derivative polynomial family

Differentiating the analytic cusp identity for `j` identifies its normalized
derivative with `q` times the derivative of the cusp representative. This gives
meromorphic cusp representatives for the functions `-η (Θj) B(j)` used in the
construction of `K_d` [rolenManuscript, §3]. The Fourier coefficient comparison
is a separate obligation.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Topology

/-- The analytic invariant's cusp representative is differentiable at every
nome arising from the upper half-plane. -/
theorem differentiableAt_levelOneJCusp_qParam (τ : UpperHalfPlane) :
    DifferentiableAt ℂ levelOneJCusp (Function.Periodic.qParam 1 τ) := by
  have hq := Function.Periodic.norm_qParam_lt_one (h := 1) one_pos τ.im_pos
  have hE := ModularFormClass.differentiableAt_cuspFunction ModularForm.E₄
    one_pos one_mem_strictPeriods_SL hq
  have hD := ModularFormClass.differentiableAt_cuspFunction CuspForm.discriminant
    one_pos one_mem_strictPeriods_SL hq
  have hD0 : cuspFunction 1 CuspForm.discriminant (Function.Periodic.qParam 1 τ) ≠ 0 := by
    rw [SlashInvariantFormClass.eq_cuspFunction _ _ one_mem_strictPeriods_SL one_ne_zero]
    exact pow_ne_zero 24 (ModularForm.eta_ne_zero τ.im_pos)
  have hfun : levelOneJCusp = fun q : ℂ =>
      cuspFunction 1 ModularForm.E₄ q ^ 3 /
        cuspFunction 1 CuspForm.discriminant q := funext levelOneJCusp_eq
  rw [hfun]
  exact (hE.pow 3).div hD hD0

private theorem hasDerivAt_qParam_one (z : ℂ) :
    HasDerivAt (Function.Periodic.qParam 1)
      (Function.Periodic.qParam 1 z * (2 * Real.pi * Complex.I)) z := by
  change HasDerivAt (fun w => Function.Periodic.qParam 1 w) _ z
  simpa [Function.Periodic.qParam] using
    ((hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I)).cexp

/-- The Euler derivative of the analytic cusp representative. -/
noncomputable def thetaLevelOneJCusp (q : ℂ) : ℂ :=
  q * deriv levelOneJCusp q

/-- The Euler derivative in the cusp nome. -/
theorem thetaLevelOneJCusp_eq (q : ℂ) :
    thetaLevelOneJCusp q = q * deriv levelOneJCusp q := (rfl)

/-- The normalized derivative is represented by the Euler derivative in the nome. -/
theorem thetaLevelOneJCusp_qParam (τ : UpperHalfPlane) :
    thetaLevelOneJCusp (Function.Periodic.qParam 1 τ) = thetaLevelOneJ τ := by
  have hchain := (differentiableAt_levelOneJCusp_qParam τ).hasDerivAt.comp
    (τ : ℂ) (hasDerivAt_qParam_one τ)
  have heq : (fun z : ℂ => levelOneJCusp (Function.Periodic.qParam 1 z))
      =ᶠ[𝓝 (τ : ℂ)] (levelOneJ ∘ ofComplex) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos] with z hz
    simpa only [Function.comp_apply, ofComplex_apply_of_im_pos hz] using
      levelOneJCusp_qParam (⟨z, hz⟩ : UpperHalfPlane)
  have hderiv := (hchain.congr_of_eventuallyEq heq.symm).deriv
  have hC : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [thetaLevelOneJ_eq, hderiv, thetaLevelOneJCusp]
  field_simp

/-- Differentiation preserves meromorphy at the cusp. -/
theorem meromorphicAt_thetaLevelOneJCusp_zero : MeromorphicAt thetaLevelOneJCusp 0 := by
  exact (MeromorphicAt.id 0).mul meromorphicAt_levelOneJCusp_zero.deriv

/-- A period-24 cusp representative for the derivative polynomial family. -/
noncomputable def etaThetaJPolynomialCusp (P : Polynomial ℤ) (t : ℂ) : ℂ :=
  -etaJPolynomialCusp P t * thetaLevelOneJCusp (t ^ 24)

/-- The derivative polynomial representative is meromorphic at the cusp. -/
theorem meromorphicAt_etaThetaJPolynomialCusp_zero (P : Polynomial ℤ) :
    MeromorphicAt (etaThetaJPolynomialCusp P) 0 := by
  have hθ : MeromorphicAt (fun t : ℂ => thetaLevelOneJCusp (t ^ 24)) 0 := by
    exact MeromorphicAt.comp_analyticAt (𝕜 := ℂ) (𝕜' := ℂ)
      (f := thetaLevelOneJCusp) (g := fun t : ℂ => t ^ 24) (x := (0 : ℂ))
      (by simpa using meromorphicAt_thetaLevelOneJCusp_zero) (analyticAt_id.pow 24)
  exact (meromorphicAt_etaJPolynomialCusp_zero P).neg.mul hθ

/-- Evaluation of the cusp representative gives the actual analytic K-family. -/
theorem etaThetaJPolynomialCusp_qParam (P : Polynomial ℤ) (τ : UpperHalfPlane) :
    etaThetaJPolynomialCusp P (Function.Periodic.qParam 24 τ) =
      etaThetaJPolynomial P τ := by
  simp only [etaThetaJPolynomialCusp, qParam_twentyFour_pow,
    etaJPolynomialCusp_qParam, thetaLevelOneJCusp_qParam,
    etaThetaJPolynomial_eq, etaJPolynomial_eq]
  ring

/-- Every derivative eta polynomial has an actual meromorphic cusp representative. -/
theorem etaThetaJPolynomial_has_meromorphic_cusp (P : Polynomial ℤ) :
    ∃ F : ℂ → ℂ, MeromorphicAt F 0 ∧ ∀ τ : UpperHalfPlane,
      F (Function.Periodic.qParam 24 τ) = etaThetaJPolynomial P τ :=
  ⟨etaThetaJPolynomialCusp P, meromorphicAt_etaThetaJPolynomialCusp_zero P,
    etaThetaJPolynomialCusp_qParam P⟩

end SptClassification
