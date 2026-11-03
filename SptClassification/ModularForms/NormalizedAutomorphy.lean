/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ApproximationConstruction

/-!
# Automorphy of the normalized smallest-parts representative

The three summands of [rolenManuscript, §2, (2.5)] have the same
weight and character. This calculation keeps the negative weight of the
inverse eta series explicit and uses the fourth power of the theta factor.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups Manifold

/-- The two Eisenstein factors use Mathlib's level-one transformation law. -/
theorem eisenstein_map_action {k : ℕ} (hk : 3 ≤ k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    ModularForm.E hk ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) =
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ k * ModularForm.E hk τ := by
  have hγ : Matrix.SpecialLinearGroup.mapGL ℝ γ ∈ 𝒮ℒ := ⟨γ, rfl⟩
  simpa only [MulAction.compHom_smul_def, Matrix.SpecialLinearGroup.mapGL,
    MonoidHom.comp_apply, zpow_natCast] using
    SlashInvariantForm.slash_action_eqn'' (f := ModularForm.E hk) hγ τ

/-- Holomorphy of the representative follows from holomorphy of its three
twisted constituents. -/
theorem SptTwistedAnalyticData.normalizedRepresentative_holomorphic
    {p Q : ℕ} [Fact Q.Prime] (A : SptTwistedAnalyticData Q) (hp : 5 ≤ p)
    (hM : MDiff A.twistedM) (hD : MDiff A.serreDerivativeP)
    (hP : MDiff A.twistedP) : MDiff (A.normalizedRepresentative p hp) := by
  have heq : A.normalizedRepresentative p hp = fun τ =>
      ModularForm.E (k := p - 1) (by omega) τ *
        (A.twistedM τ - A.serreDerivativeP τ / 12) +
      ModularForm.E (k := p + 1) (by omega) τ * A.twistedP τ / 288 :=
    funext (A.normalizedRepresentative_apply p hp)
  rw [heq]
  simp only [div_eq_mul_inv]
  exact ((ModularForm.E (k := p - 1) (by omega)).holo'.mul
    (hM.sub (hD.mul mdifferentiable_const))).add
      (((ModularForm.E (k := p + 1) (by omega)).holo'.mul hP).mul mdifferentiable_const)

/-- Multiplying weight `3/2` and `-1/2` forms by the two even-weight
Eisenstein series gives the same weight `p+1/2` theta multiplier. -/
theorem normalizedThetaFactors {p : ℕ} (hp : Odd p) {j d : ℂ}
    (hj : j ≠ 0) (hfour : j ^ 4 = d ^ 2) :
    d ^ (p - 1) * j ^ 3 = j ^ (2 * p + 1) ∧
      d ^ (p + 1) / j = j ^ (2 * p + 1) := by
  obtain ⟨m, rfl⟩ := hp
  have heven : 2 * m + 1 - 1 = 2 * m := by omega
  have hplus : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  rw [heven, hplus, pow_mul, pow_mul, ← hfour]
  constructor
  · ring
  · apply (div_eq_iff hj).2
    ring

/-- The manuscript's normalized linear combination transforms with weight
`p+1/2` once its three constituent forms have their usual transformation
laws. The Eisenstein and theta identities are stated independently of the
normalized function, so this is a deduction rather than an approximation
assumption. -/
theorem SptTwistedAnalyticData.normalizedRepresentative_map_action
    {p Q N : ℕ} [Fact p.Prime] [Fact Q.Prime]
    (A : SptTwistedAnalyticData Q) (hp : 5 ≤ p)
    (χ : CongruenceSubgroup.Gamma0 N → ℂ)
    (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane)
    (hj : jacobiTheta (2 * (τ : ℂ)) ≠ 0)
    (hjγ : jacobiTheta (2 * (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ : UpperHalfPlane) : ℂ)) ≠ 0)
    (hfour :
      (jacobiTheta (2 * (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) ^ 4 =
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) τ) ^ 2)
    (hM : A.twistedM ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) = χ γ *
      (jacobiTheta (2 * (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) ^ 3 * A.twistedM τ)
    (hD : A.serreDerivativeP ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) = χ γ *
      (jacobiTheta (2 * (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) ^ 3 * A.serreDerivativeP τ)
    (hP : A.twistedP ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) = χ γ /
      (jacobiTheta (2 * (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) * A.twistedP τ) :
    A.normalizedRepresentative p hp ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) =
      χ γ * standardProgressionFactor p true (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) τ *
        A.normalizedRepresentative p hp τ := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨hm, hp'⟩ := normalizedThetaFactors hodd (div_ne_zero hjγ hj) hfour
  rw [A.normalizedRepresentative_apply, A.normalizedRepresentative_apply,
    hM, hD, hP]
  have he (k : ℕ) (hk : 3 ≤ k) : ModularForm.E hk ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) =
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) τ) ^ k *
        ModularForm.E hk τ := by
    exact eisenstein_map_action hk (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) τ
  rw [he, he]
  rw [standardProgressionFactor_half]
  linear_combination
    (χ γ * ModularForm.E (k := p - 1) (by omega) τ *
      (A.twistedM τ - A.serreDerivativeP τ / 12)) * hm +
    (χ γ * ModularForm.E (k := p + 1) (by omega) τ * A.twistedP τ / 288) * hp'

end SptClassification
