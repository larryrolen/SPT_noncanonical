/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterTwelveModular
public import SptClassification.ModularForms.ActualNormalizedAutomorphy
public import SptClassification.ModularForms.ActualTwistTransformation
public import SptClassification.ModularForms.IntegralSlashCusps
public import SptClassification.ModularForms.ThetaMultiplier

/-!
# Integral automorphy of the actual normalized fourth power

The quadratic character and theta multiplier cancel after taking the fourth
power of the representative in [rolenManuscript, §2, (2.5)].
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups ModularForm

/-- The fourth power of the actual representative has weight `4p+2` and
trivial character at level `576 Q⁴`. -/
theorem sptTwistedAnalyticData_normalizedFourthPower_map_action
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p) (hQ : Odd Q)
    (γ : CongruenceSubgroup.Gamma0 (576 * Q ^ 4)) (τ : UpperHalfPlane) :
    (sptTwistedAnalyticData Q).normalizedRepresentative p hp (γ • τ) ^ 4 =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ))) τ ^ (4 * p + 2) *
        (sptTwistedAnalyticData Q).normalizedRepresentative p hp τ ^ 4 := by
  have h12 : 12 ∣ 576 * Q ^ 4 := ⟨48 * Q ^ 4, by ring⟩
  have h4 : 4 ∣ 576 * Q ^ 4 := ⟨144 * Q ^ 4, by ring⟩
  have hmap := sptTwistedAnalyticData_normalizedRepresentative_map_action hp
    (characterTwelveGamma0 h12) theta_twice_ne_zero
    (theta_multiplier_fourth_of_level_dvd h4)
    (by simpa only [characterTwelveGamma0_apply] using
      sptTwistedAnalyticData_twistedM_map_action Q hQ)
    (by simpa only [characterTwelveGamma0_apply] using
      sptTwistedAnalyticData_twistedP_map_action Q hQ) γ τ
  have hχ : characterTwelveGamma0 h12 γ ^ 4 = 1 := by
    calc
      _ = (characterTwelveGamma0 h12 γ ^ 2) ^ 2 := by ring
      _ = 1 := by rw [characterTwelveGamma0_sq]; norm_num
  have htheta := theta_multiplier_fourth_of_level_dvd h4 γ τ
  change (jacobiTheta (2 * ((γ : SL(2, ℤ)) • τ : UpperHalfPlane)) /
    jacobiTheta (2 * (τ : ℂ))) ^ 4 =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ (γ : SL(2, ℤ))) τ ^ 2 at htheta
  rw [hmap, mul_pow, mul_pow, hχ, one_mul, standardProgressionFactor_half]
  rw [← pow_mul, Nat.mul_comm (2 * p + 1) 4, pow_mul,
    htheta, ← pow_mul]
  congr 2
  omega

/-- The integral slash formulation of the fourth-power transformation. -/
theorem sptTwistedAnalyticData_normalizedFourthPower_slash
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p) (hQ : Odd Q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 (576 * Q ^ 4)) :
    (fun τ => (sptTwistedAnalyticData Q).normalizedRepresentative p hp τ ^ 4)
      ∣[((4 * p + 2 : ℕ) : ℤ)] γ =
    (fun τ => (sptTwistedAnalyticData Q).normalizedRepresentative p hp τ ^ 4) := by
  funext τ
  rw [integral_slash_nat_apply]
  have h := sptTwistedAnalyticData_normalizedFourthPower_map_action hp hQ ⟨γ, hγ⟩ τ
  change (sptTwistedAnalyticData Q).normalizedRepresentative p hp (γ • τ) ^ 4 =
    denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ ^ (4 * p + 2) *
      (sptTwistedAnalyticData Q).normalizedRepresentative p hp τ ^ 4 at h
  rw [h]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (denom_ne_zero _ τ))

end SptClassification
