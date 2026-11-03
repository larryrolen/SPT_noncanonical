/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.EtaAutomorphy

/-!
# Generator criterion for inverse-eta weight-zero forms

For a holomorphic function with the inverse eta multiplier, the product with
eta is invariant under the full modular group. Its invariance can be checked
on the inversion and translation generators. This reduces the remaining
modular transformation of the analytic prime Hecke expression to inversion
[apostol1990, Chapter 3].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- A function whose product with eta is fixed by the two standard generators
has the full inverse-eta transformation law at weight `-1/2`. -/
theorem inverseEta_map_action_of_generator_products
    (f : UpperHalfPlane → ℂ)
    (hS : ∀ τ : UpperHalfPlane,
      f (ModularGroup.S • τ) *
        ModularForm.eta ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) =
        f τ * ModularForm.eta τ)
    (hT : ∀ τ : UpperHalfPlane,
      f (ModularGroup.T • τ) *
        ModularForm.eta ((ModularGroup.T • τ : UpperHalfPlane) : ℂ) =
        f τ * ModularForm.eta τ)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ 𝒮ℒ) (τ : UpperHalfPlane) :
    f (γ • τ) = (etaAutomorphyFactor γ τ)⁻¹ * f τ := by
  obtain ⟨g, rfl⟩ := hγ
  have hg : g ∈ Subgroup.closure
      ({ModularGroup.S, ModularGroup.T} :
        Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    simp [SpecialLinearGroup.SL2Z_generators]
  have hinv : ∀ x : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      x ∈ Subgroup.closure
        ({ModularGroup.S, ModularGroup.T} :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) →
      ∀ z : UpperHalfPlane,
        f (x • z) * ModularForm.eta ((x • z : UpperHalfPlane) : ℂ) =
          f z * ModularForm.eta z := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | one =>
        intro z
        simp
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hS
        · exact hT
    | mul x y _ _ ix iy =>
        intro z
        simpa only [mul_smul] using (ix (y • z)).trans (iy z)
    | inv x _ ix =>
        intro z
        have h := ix (x⁻¹ • z)
        simpa only [smul_smul, mul_inv_cancel, one_smul] using h.symm
  have h := hinv g hg τ
  have heq : f (g • τ) * etaAutomorphyFactor (Matrix.SpecialLinearGroup.mapGL ℝ g) τ =
      f τ := by
    apply mul_right_cancel₀ (ModularForm.eta_ne_zero τ.im_pos)
    calc
      (f (g • τ) * etaAutomorphyFactor
          (Matrix.SpecialLinearGroup.mapGL ℝ g) τ) * ModularForm.eta τ =
        f (g • τ) * ModularForm.eta ((g • τ : UpperHalfPlane) : ℂ) := by
          rw [mul_assoc, etaAutomorphyFactor_mul_eta]
          rfl
      _ = f τ * ModularForm.eta τ := h
  have hfac := etaAutomorphyFactor_ne_zero
    (Matrix.SpecialLinearGroup.mapGL ℝ g) τ
  calc
    f (g • τ) = f (g • τ) *
        (etaAutomorphyFactor (Matrix.SpecialLinearGroup.mapGL ℝ g) τ *
          (etaAutomorphyFactor (Matrix.SpecialLinearGroup.mapGL ℝ g) τ)⁻¹) := by
            simp [hfac]
    _ = (etaAutomorphyFactor (Matrix.SpecialLinearGroup.mapGL ℝ g) τ)⁻¹ * f τ := by
      rw [← mul_assoc, heq]
      ring

end SptClassification
