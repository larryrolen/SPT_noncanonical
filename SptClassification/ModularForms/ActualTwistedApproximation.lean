/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ActualNormalizedCusps
public import SptClassification.ModularForms.ActualApproximation
public import SptClassification.ModularForms.ActualTwistTransformation

/-!
# The actual approximation with its transformation laws supplied

The two filtered transformation laws now follow from the named untwisted
literature inputs and the proved finite-filter calculation. Meromorphy at
cusps follows from the actual coefficient estimates and fourth-power automorphy.
-/

public section

namespace SptClassification

open UpperHalfPlane
open scoped MatrixGroups

/-- Construct the actual approximation from its remaining cusp law. -/
noncomputable def actualApproximationOfCuspLaw
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p) (hQ : Odd Q)
    (hcusps : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∃ width : ℕ, 0 < width ∧ ∃ G : ℂ → ℂ, MeromorphicAt G 0 ∧
        ∀ τ : UpperHalfPlane,
          G (Function.Periodic.qParam width τ) =
            (sptTwistedAnalyticData Q).normalizedRepresentative p hp (γ • τ) ^ 4 /
              (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ) ^ (4 * p + 2)) :
    SptModularApproximation p Q hp :=
  actualApproximationOfAnalyticLaws hp
    (sptTwistedAnalyticData_twistedM_map_action Q hQ)
    (sptTwistedAnalyticData_twistedP_map_action Q hQ) hcusps

/-- The remaining cusp law suffices for propagation. Transformation,
holomorphy, Fourier normalization and coefficient transport are deductions.
The cusp hypothesis is explicit, not an admitted manuscript conclusion. -/
theorem propagation_of_actual_cusp_law
    (p b : ℕ) (hpprime : p.Prime) (hp : 5 ≤ p) (hb : b < p)
    (hnotcanonical : ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) ≠ 0)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
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
  have hodd : Odd Q := hQ.odd_of_ne_two (by
    intro htwo
    apply havoid
    rw [htwo]
    exact dvd_mul_of_dvd_left (by decide : 2 ∣ 6) p)
  exact actualApproximationOfCuspLaw hp hodd (hcusps Q havoid)

/-- The actual manuscript approximation, constructed from the partition-defined
series and the named classical literature inputs. -/
noncomputable def actualSptModularApproximation
    {p Q : ℕ} [Fact p.Prime] [Fact Q.Prime] (hp : 5 ≤ p) (hQ : Odd Q) :
    SptModularApproximation p Q hp :=
  actualApproximationOfCuspLaw hp hQ
    (sptTwistedAnalyticData_normalizedRepresentative_cusps hp hQ)

end SptClassification
