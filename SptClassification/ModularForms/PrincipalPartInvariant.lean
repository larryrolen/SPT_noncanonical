/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# An analytic level-one modular invariant

The quotient `E₄³/Δ` supplies the modular invariant used in the manuscript's
eta-polynomial principal-part construction [rolenManuscript, §3]. This module
establishes its level-one invariance from Mathlib's normalized Eisenstein series
and discriminant. Its integral Fourier expansion is handled separately.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

/-- The analytic level-one modular invariant `E₄³/Δ`, with the normalization
whose leading Fourier term is `q⁻¹`. -/
noncomputable def levelOneJ (τ : UpperHalfPlane) : ℂ :=
  ModularForm.E₄ τ ^ 3 / CuspForm.discriminant τ

/-- The quotient formula for the normalized analytic invariant. -/
theorem levelOneJ_eq (τ : UpperHalfPlane) :
    levelOneJ τ = ModularForm.E₄ τ ^ 3 / CuspForm.discriminant τ :=
  (rfl)

/-- The modular invariant is holomorphic in the upper half-plane. -/
theorem levelOneJ_mdifferentiable : MDiff levelOneJ := by
  have hD0 : ∀ τ : UpperHalfPlane, CuspForm.discriminant τ ≠ 0 := by
    intro τ
    change ModularForm.discriminant τ ≠ 0
    exact pow_ne_zero 24 (ModularForm.eta_ne_zero τ.im_pos)
  exact (ModularForm.E₄.holo'.pow 3).div
    CuspForm.discriminant.holo' hD0

theorem levelOneJ_invariant (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ)
    (τ : UpperHalfPlane) :
    levelOneJ (γ • τ) = levelOneJ τ := by
  have hE := SlashInvariantForm.slash_action_eqn''
    (f := ModularForm.E₄) hγ τ
  have hD := SlashInvariantForm.slash_action_eqn''
    (f := CuspForm.discriminant) hγ τ
  have hn := UpperHalfPlane.denom_ne_zero γ τ
  simp only [levelOneJ, hE, hD]
  have hD0 : CuspForm.discriminant τ ≠ 0 := by
    change ModularForm.discriminant τ ≠ 0
    exact pow_ne_zero 24 (ModularForm.eta_ne_zero τ.im_pos)
  field_simp [hn, hD0]

end SptClassification
