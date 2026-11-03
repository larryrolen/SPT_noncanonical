/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ThetaTranslation
public import SptClassification.ModularForms.MockCompletionTransformation
public import SptClassification.ModularForms.ScaledEtaTransformation

/-!
# Transformation of the actual filtered completion

The square-invariance of the manuscript's selector and the classical
rational-translation calculation give the filtered transformation law.
The proved shadow cancellation identifies the filtered completion with the
actual holomorphic function, without applying a positive-weight holomorphic
twisting theorem to a harmonic function.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- Restrict a congruence transformation to a divisor of its level. -/
def gamma0Restrict {N L : ℕ} (h : N ∣ L)
    (γ : CongruenceSubgroup.Gamma0 L) : CongruenceSubgroup.Gamma0 N :=
  ⟨γ, by
    apply CongruenceSubgroup.Gamma0_mem.mpr
    have hγ := CongruenceSubgroup.Gamma0_mem.mp γ.property
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
    exact (show (N : ℤ) ∣ (L : ℤ) by exact_mod_cast h).trans hγ⟩

@[simp] theorem gamma0Restrict_coe {N L : ℕ} (h : N ∣ L)
    (γ : CongruenceSubgroup.Gamma0 L) :
    (gamma0Restrict h γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) = γ := (rfl)

@[simp] theorem gamma0Restrict_smul {N L : ℕ} (h : N ∣ L)
    (γ : CongruenceSubgroup.Gamma0 L) (τ : UpperHalfPlane) :
    gamma0Restrict h γ • τ = γ • τ := (rfl)

/-- The actual filtered mock completion has the required weight `3/2` law. -/
theorem sptTwistedAnalyticData_twistedM_map_action
    (Q : ℕ) [Fact Q.Prime] (hQ : Odd Q)
    (γ : CongruenceSubgroup.Gamma0 (576 * Q ^ 4)) (τ : UpperHalfPlane) :
    (sptTwistedAnalyticData Q).twistedM (γ • τ) =
      (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) *
      (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) ^ 3 * (sptTwistedAnalyticData Q).twistedM τ := by
  let χ : ZMod 576 → ℂ := fun d =>
    (characterTwelveResidue (ZMod.castHom (by decide : 12 ∣ 576) (ZMod 12) d) : ℂ)
  have hχ (d : ℤ) : χ (d : ZMod 576) = (characterTwelve d : ℂ) := by
    simp [χ, characterTwelve_eq_residue]
  let γ' : CongruenceSubgroup.Gamma0 (576 * Q ^ 2) :=
    gamma0Restrict (show 576 * Q ^ 2 ∣ 576 * Q ^ 4 from
      ⟨Q ^ 2, by ring⟩) γ
  have h := fourierFilter_theta_map_action (by norm_num : 0 < 576) (by decide)
    hQ (negativeSquareResidueSelector Q)
    (negativeSquareResidueSelector_mul_square Q) sptCompletion χ (3 : ℤ)
    (fun δ z => by
      have ha : (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z = δ • z := rfl
      simpa only [ha, hχ, zpow_ofNat, standardProgressionFactor_half,
        show 2 * 1 + 1 = 3 by decide] using
        ahlgrenAndersen_sptCompletion_map_action δ z) γ' τ
  simpa only [γ', gamma0Restrict_smul, gamma0Restrict_coe, hχ, zpow_ofNat,
    fourierFilter_sptCompletion] using h

/-- The actual filtered partition function has the required weight `-1/2` law. -/
theorem sptTwistedAnalyticData_twistedP_map_action
    (Q : ℕ) [Fact Q.Prime] (hQ : Odd Q)
    (γ : CongruenceSubgroup.Gamma0 (576 * Q ^ 4)) (τ : UpperHalfPlane) :
    (sptTwistedAnalyticData Q).twistedP (γ • τ) =
      (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) /
      (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) * (sptTwistedAnalyticData Q).twistedP τ := by
  let χ : ZMod 576 → ℂ := fun d =>
    (characterTwelveResidue (ZMod.castHom (by decide : 12 ∣ 576) (ZMod 12) d) : ℂ)
  have hχ (d : ℤ) : χ (d : ZMod 576) = (characterTwelve d : ℂ) := by
    simp [χ, characterTwelve_eq_residue]
  let γ' : CongruenceSubgroup.Gamma0 (576 * Q ^ 2) :=
    gamma0Restrict (show 576 * Q ^ 2 ∣ 576 * Q ^ 4 from
      ⟨Q ^ 2, by ring⟩) γ
  have h := fourierFilter_theta_map_action (by norm_num : 0 < 576) (by decide)
    hQ (negativeSquareResidueSelector Q)
    (negativeSquareResidueSelector_mul_square Q) scaledPartitionFunction χ (-1 : ℤ)
    (fun δ z => by simpa only [hχ] using scaledPartitionFunction_map_action δ z) γ' τ
  simpa only [γ', gamma0Restrict_smul, gamma0Restrict_coe, hχ, zpow_neg_one,
    ← sptTwistedAnalyticData_twistedP_eq, div_eq_mul_inv] using h

end SptClassification
