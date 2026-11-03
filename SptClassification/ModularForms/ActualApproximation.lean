/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.CharacterTwelveModular
public import SptClassification.ModularForms.ActualNormalizedAutomorphy
public import SptClassification.ModularForms.ApproximationConstruction
public import SptClassification.ModularForms.ApproximationPropagation
public import SptClassification.ModularForms.ThetaMultiplier

/-!
# The actual approximation from its remaining analytic laws

This assembles [rolenManuscript, §2, (2.5)] with its actual character,
Fourier coefficients and Serre derivative. The transformation laws of the
two filtered functions and meromorphy at cusps remain explicit
hypotheses. No existence of an approximation is admitted here.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- Construct the manuscript's actual approximation at level `576 Q⁴`.
The derivative transformation and holomorphy are proved deductions; only
the remaining analytic laws are supplied. -/
noncomputable def actualApproximationOfAnalyticLaws
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p)
    (hM : ∀ (γ : CongruenceSubgroup.Gamma0 (576 * Q ^ 4)) (τ : UpperHalfPlane),
      (sptTwistedAnalyticData Q).twistedM (γ • τ) =
        (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) *
        (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
          jacobiTheta (2 * (τ : ℂ))) ^ 3 * (sptTwistedAnalyticData Q).twistedM τ)
    (hP : ∀ (γ : CongruenceSubgroup.Gamma0 (576 * Q ^ 4)) (τ : UpperHalfPlane),
      (sptTwistedAnalyticData Q).twistedP (γ • τ) =
        (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) /
        (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
          jacobiTheta (2 * (τ : ℂ))) * (sptTwistedAnalyticData Q).twistedP τ)
    (hcusps : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ width : ℕ, 0 < width ∧ ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
        ∀ τ : UpperHalfPlane,
          G (Function.Periodic.qParam width τ) =
            (sptTwistedAnalyticData Q).normalizedRepresentative p hp (γ • τ) ^ 4 /
              (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ (4 * p + 2)) :
    SptModularApproximation p Q hp := by
  have h12 : 12 ∣ 576 * Q ^ 4 := ⟨48 * Q ^ 4, by ring⟩
  apply (sptTwistedAnalyticData Q).approximationOfModularity hp (576 * Q ^ 4)
    (mul_pos (by norm_num) (pow_pos (Fact.out : Q.Prime).pos _))
    ⟨144 * Q ^ 4, by ring⟩ (dvd_refl _)
    (characterTwelveGamma0 h12) (characterTwelveAtLevel h12)
    (characterTwelveGamma0_eq_nebentypus h12) (characterTwelveGamma0_sq h12)
    (sptTwistedAnalyticData_normalizedRepresentative_holomorphic p Q hp) _ hcusps
  apply sptTwistedAnalyticData_normalizedRepresentative_map_action hp
    (characterTwelveGamma0 h12) theta_twice_ne_zero
    (theta_multiplier_fourth_of_level_dvd ⟨144 * Q ^ 4, by ring⟩)
  · simpa only [characterTwelveGamma0_apply] using hM
  · simpa only [characterTwelveGamma0_apply] using hP

/-- The actual analytic laws imply propagation for the partition-defined
smallest-parts function. The remaining transformation and cusp hypotheses
are explicit; this does not close the original manuscript theorem. -/
theorem propagation_of_actual_analytic_laws
    (p b : ℕ) (hpprime : p.Prime) (hp : 5 ≤ p) (hb : b < p)
    (hnotcanonical : ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) ≠ 0)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (hM : ∀ (Q : ℕ) [Fact Q.Prime], ¬Q ∣ 6 * p → ∀ (γ : CongruenceSubgroup.Gamma0 (576 * Q ^ 4)) (τ : UpperHalfPlane),
      (sptTwistedAnalyticData Q).twistedM (γ • τ) =
        (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) *
        (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
          jacobiTheta (2 * (τ : ℂ))) ^ 3 * (sptTwistedAnalyticData Q).twistedM τ)
    (hP : ∀ (Q : ℕ) [Fact Q.Prime], ¬Q ∣ 6 * p → ∀ (γ : CongruenceSubgroup.Gamma0 (576 * Q ^ 4)) (τ : UpperHalfPlane),
      (sptTwistedAnalyticData Q).twistedP (γ • τ) =
        (characterTwelve (((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℂ) /
        (jacobiTheta (2 * ((γ • τ : UpperHalfPlane) : ℂ)) /
          jacobiTheta (2 * (τ : ℂ))) * (sptTwistedAnalyticData Q).twistedP τ)
    (hcusps : ∀ (Q : ℕ) [Fact Q.Prime], ¬Q ∣ 6 * p → ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ width : ℕ, 0 < width ∧ ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
        ∀ τ : UpperHalfPlane,
          G (Function.Periodic.qParam width τ) =
            (sptTwistedAnalyticData Q).normalizedRepresentative p hp (γ • τ) ^ 4 /
              (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ (4 * p + 2))
    (N : ℕ)
    (hclass : @legendreSym p ⟨hpprime⟩ (1 - 24 * (N : ℤ)) =
      @legendreSym p ⟨hpprime⟩ (1 - 24 * (b : ℤ))) :
    p ∣ spt N := by
  let : Fact p.Prime := ⟨hpprime⟩
  apply propagation_of_approximation p b hpprime hp hb hnotcanonical hspt ?_ N hclass
  refine ⟨fun Q hQ havoid => ?_⟩
  let : Fact Q.Prime := ⟨hQ⟩
  exact actualApproximationOfAnalyticLaws hp
    (hM Q havoid) (hP Q havoid) (hcusps Q havoid)

end SptClassification
