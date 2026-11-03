/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.PrincipalPartPolynomial
public import SptClassification.ModularForms.EtaUnipotent

/-!
# The canonical Dedekind eta automorphy factor

The nonzero eta function defines its automorphy factor without a new choice of
square-root branches. Translation and inversion recover the classical
normalizations [apostol1990, Chapter 3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- The canonical automorphy factor of the actual nonvanishing eta function. -/
noncomputable def etaAutomorphyFactor (γ : GL (Fin 2) ℝ) (τ : UpperHalfPlane) : ℂ :=
  ModularForm.eta (γ • τ : UpperHalfPlane) / ModularForm.eta τ

/-- The eta factor is nonzero at every upper-half-plane point. -/
theorem etaAutomorphyFactor_ne_zero (γ : GL (Fin 2) ℝ) (τ : UpperHalfPlane) :
    etaAutomorphyFactor γ τ ≠ 0 :=
  div_ne_zero (ModularForm.eta_ne_zero (γ • τ).im_pos) (ModularForm.eta_ne_zero τ.im_pos)

/-- The actual eta function transforms by its canonical factor. -/
theorem etaAutomorphyFactor_mul_eta (γ : GL (Fin 2) ℝ) (τ : UpperHalfPlane) :
    etaAutomorphyFactor γ τ * ModularForm.eta τ =
      ModularForm.eta (γ • τ : UpperHalfPlane) := by
  exact div_mul_cancel₀ _ (ModularForm.eta_ne_zero τ.im_pos)

/-- Identity normalization of the eta factor. -/
@[simp] theorem etaAutomorphyFactor_one (τ : UpperHalfPlane) :
    etaAutomorphyFactor 1 τ = 1 := by
  simp [etaAutomorphyFactor, ModularForm.eta_ne_zero τ.im_pos]

/-- The eta factor satisfies the exact automorphy cocycle identity. -/
theorem etaAutomorphyFactor_mul (γ δ : GL (Fin 2) ℝ) (τ : UpperHalfPlane) :
    etaAutomorphyFactor (γ * δ) τ =
      etaAutomorphyFactor γ (δ • τ) * etaAutomorphyFactor δ τ := by
  simp only [etaAutomorphyFactor, mul_smul]
  field_simp [ModularForm.eta_ne_zero (δ • τ).im_pos]

/-- The translation multiplier is the specified twenty-fourth root of unity. -/
theorem etaAutomorphyFactor_upperUnipotent (n : ℤ) (τ : UpperHalfPlane) :
    etaAutomorphyFactor (Matrix.SpecialLinearGroup.mapGL ℝ (upperUnipotent n)) τ =
      Complex.exp (Real.pi * Complex.I * n / 12) := by
  change ModularForm.eta (upperUnipotent n • τ : UpperHalfPlane) / ModularForm.eta τ = _
  rw [upperUnipotent_apply, eta_add_int]
  exact mul_div_cancel_right₀ _ (ModularForm.eta_ne_zero τ.im_pos)

/-- Inversion fixes the standard principal-square-root eta normalization. -/
theorem eta_inversion_factor (τ : UpperHalfPlane) :
    ModularForm.eta (-1 / (τ : ℂ)) / ModularForm.eta τ =
      Complex.I.sqrt⁻¹ * (τ : ℂ).sqrt := by
  rw [eta_neg_inv τ.im_pos]
  exact mul_div_cancel_right₀ _ (ModularForm.eta_ne_zero τ.im_pos)

end SptClassification
