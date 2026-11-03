/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ActualNormalizedRepresentative
public import SptClassification.ModularForms.HalfIntegralSerre
import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold

/-!
# Automorphy from the two actual filtered functions

The derivative transformation in [rolenManuscript, §2, (2.5)] is a
deduction from that of the filtered inverse eta function. Only the two
filtered functions and the theta multiplier need transformation inputs.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped Manifold MatrixGroups

/-- Holomorphy of the theta function in the manuscript's nome. -/
theorem mdifferentiable_theta_twice :
    MDiff (fun τ : UpperHalfPlane => jacobiTheta (2 * (τ : ℂ))) := by
  intro τ
  have him : 0 < (2 * (τ : ℂ)).im := by
    simpa using mul_pos (by norm_num : (0 : ℝ) < 2) τ.im_pos
  exact (differentiableAt_jacobiTheta him).mdifferentiableAt.comp τ
    (mdifferentiableAt_const.mul τ.mdifferentiable_coe)

/-- The actual representative transforms once the two filtered functions do.
No derivative transformation law is supplied as a premise. -/
theorem sptTwistedAnalyticData_normalizedRepresentative_map_action
    {p Q N : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p)
    (χ : CongruenceSubgroup.Gamma0 N → ℂ)
    (hTheta : ∀ τ : UpperHalfPlane, jacobiTheta (2 * (τ : ℂ)) ≠ 0)
    (hfour : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane),
      (jacobiTheta (2 * (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ : UpperHalfPlane) : ℂ)) /
        jacobiTheta (2 * (τ : ℂ))) ^ 4 =
      denom (Matrix.SpecialLinearGroup.mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)) τ ^ 2)
    (hM : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane),
      (sptTwistedAnalyticData Q).twistedM (γ • τ) = χ γ *
        (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
          jacobiTheta (2 * (τ : ℂ))) ^ 3 * (sptTwistedAnalyticData Q).twistedM τ)
    (hP : ∀ (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane),
      (sptTwistedAnalyticData Q).twistedP (γ • τ) = χ γ /
        (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
          jacobiTheta (2 * (τ : ℂ))) * (sptTwistedAnalyticData Q).twistedP τ)
    (γ : CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    (sptTwistedAnalyticData Q).normalizedRepresentative p hp (γ • τ) =
      χ γ * standardProgressionFactor p true γ τ *
        (sptTwistedAnalyticData Q).normalizedRepresentative p hp τ := by
  apply (sptTwistedAnalyticData Q).normalizedRepresentative_map_action hp χ γ τ
    (hTheta τ) (hTheta (γ • τ)) (hfour γ τ) (hM γ τ) _ (hP γ τ)
  rw [sptTwistedAnalyticData_serreDerivativeP_eq,
    ← sptTwistedAnalyticData_twistedP_eq]
  have h := serreDerivative_map_of_negative_half_weight
    (sptTwistedAnalyticData Q).twistedP (fun z => jacobiTheta (2 * (z : ℂ)))
    (sptTwistedAnalyticData_twistedP_holomorphic Q) mdifferentiable_theta_twice
    hTheta γ (χ γ)
    (fun z => jacobiTheta (2 * (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) • z : UpperHalfPlane) : ℂ)) /
      jacobiTheta (2 * (z : ℂ)))
    (fun z => (div_mul_cancel₀ _ (hTheta z)).symm)
    (hfour γ) (hP γ) τ
  simpa only [neg_div] using h

end SptClassification
