/- Assembled by AxiomProver. -/

module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Holomorphic discriminant pole clearing

Multiplication by a discriminant power raises the weight of an analytic
function with a modular transformation law. Cusp boundedness is deliberately
a separate obligation, as in the clearing argument of [rolenManuscript, §4].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups ModularForm Manifold

/-- The transformation law for the actual discriminant on integral matrices. -/
theorem discriminant_transform (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (z : UpperHalfPlane) :
    ModularForm.discriminant (γ • z) =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) z ^ (12 : ℕ) *
        ModularForm.discriminant z := by
  change CuspForm.discriminant (γ • z) =
    denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) z ^ (12 : ℕ) * CuspForm.discriminant z
  have hγ : Matrix.SpecialLinearGroup.mapGL ℝ γ ∈ 𝒮ℒ := ⟨γ, rfl⟩
  simpa only [MulAction.compHom_smul_def, Matrix.SpecialLinearGroup.mapGL,
    MonoidHom.comp_apply, zpow_ofNat] using
    SlashInvariantForm.slash_action_eqn'' (f := CuspForm.discriminant) hγ z

/-- Bundle the weight obtained by multiplying by a discriminant power.
The input law concerns the actual function, with no cusp hypothesis. -/
noncomputable def discriminantPoleClearing {N k : ℕ} (f : ℂ → ℂ) (m : ℕ)
    (htrans : ∀ (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane),
      f ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ
          (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ k * f z) :
    SlashInvariantForm ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)) ((12 * m + k : ℕ) : ℤ) where
  toFun z := ModularForm.discriminant z ^ m * f z
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    change (fun z : UpperHalfPlane => ModularForm.discriminant z ^ m * f z)
      ∣[((12 * m + k : ℕ) : ℤ)] γ = _
    funext z
    rw [ModularForm.SL_slash_apply, discriminant_transform, htrans ⟨γ, hγ⟩]
    simp only [zpow_neg, zpow_natCast, mul_pow, pow_add, pow_mul]
    have hden := denom_ne_zero γ z
    field_simp
    simp only [Matrix.SpecialLinearGroup.mapGL, MonoidHom.comp_apply]
    rw [show Int.castRingHom ℝ = algebraMap ℤ ℝ from Subsingleton.elim _ _]
    ring

@[simp] theorem discriminantPoleClearing_apply {N k : ℕ} (f : ℂ → ℂ) (m : ℕ)
    (htrans : ∀ (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane),
      f ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ
          (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ k * f z)
    (z : UpperHalfPlane) :
    discriminantPoleClearing f m htrans z = ModularForm.discriminant z ^ m * f z :=
  (rfl)

/-- Analyticity of the interior function supplies holomorphy of its clearing. -/
theorem discriminantPoleClearing_holomorphic {N k : ℕ} (f : ℂ → ℂ) (m : ℕ)
    (htrans : ∀ (g : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane),
      f ((g : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) =
        denom (Matrix.SpecialLinearGroup.mapGL ℝ
          (g : Matrix.SpecialLinearGroup (Fin 2) ℤ)) z ^ k * f z)
    (hf : AnalyticOnNhd ℂ f {z | 0 < z.im}) :
    MDiff (discriminantPoleClearing f m htrans) := by
  have hf' : MDiff (fun z : UpperHalfPlane => f z) := by
    intro z
    apply mdifferentiableAt_iff.mpr
    apply (hf z z.im_pos).differentiableAt.congr_of_eventuallyEq
    filter_upwards [eventuallyEq_coe_comp_ofComplex z.im_pos] with w hw
    exact congrArg f hw
  exact (CuspForm.discriminant.holo'.pow m).mul hf'

end SptClassification
