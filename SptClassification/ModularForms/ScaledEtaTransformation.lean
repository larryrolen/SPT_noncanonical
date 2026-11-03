/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ScaledGeneratingSeries
public import SptClassification.ModularForms.ThetaMultiplier
public import SptClassification.Arithmetic.CharacterTwelveModular

/-!
# The scaled eta transformation law

The classical modularity of `η(24τ)` is stated explicitly in
[ahlgrenBringmannLovejoy2011, §3, immediately after (3.7), PDF p. 8].
The inverse law is a deduction, using the quadratic character.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- The transformation part of the stated membership
`η(24τ) ∈ M_{1/2}(Γ₀(576), (12/·))` in
[ahlgrenBringmannLovejoy2011, §3, immediately after (3.7), PDF p. 8].
The theta convention is `Θ(τ) = jacobiTheta (2τ)`.
This literature premise concerns eta alone. -/
theorem ahlgrenBringmannLovejoy_eta_twenty_four_map_action
    (γ : CongruenceSubgroup.Gamma0 576) (τ : UpperHalfPlane) :
    ModularForm.eta (24 * ((γ • τ : UpperHalfPlane) : ℂ)) =
      (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) *
      (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) * ModularForm.eta (24 * (τ : ℂ)) := by
  sorry

/-- Inverting the eta law gives the actual partition function's weight `-1/2`. -/
theorem scaledPartitionFunction_map_action
    (γ : CongruenceSubgroup.Gamma0 576) (τ : UpperHalfPlane) :
    scaledPartitionFunction (γ • τ) =
      (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) *
      (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) ^ (-1 : ℤ) * scaledPartitionFunction τ := by
  have hχ := characterTwelveGamma0_sq (by decide : 12 ∣ 576) γ
  rw [characterTwelveGamma0_apply] at hχ
  have hi : (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ)⁻¹ =
      (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hχ
  simp only [scaledPartitionFunction_eq_eta,
    ahlgrenBringmannLovejoy_eta_twenty_four_map_action, mul_inv, hi, zpow_neg_one]

end SptClassification
