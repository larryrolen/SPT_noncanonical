/- Assembled by AxiomProver. -/

module

public import SptClassification.Classification.RealizedGeometry
public import SptClassification.ModularForms.ProgressionSlash
public import SptClassification.QSeries.AnalyticConstantTerms

/-!
# Classification from powered progression data

The generic progression transport is derived from pointwise powered slash,
local integrality and rational Laurent descent. The actual smallest-parts
approximation and the remaining analytic and geometric inputs stay explicit.
[rolenManuscript, Sections 2, 4--5]
-/

public section

namespace SptClassification

variable {A : ℕ → Subring ℚ} {C K : ℕ → Type*}
variable [∀ p, CommRing (C p)] [∀ p, Field (K p)]
variable [∀ p, Algebra (A p) (C p)] [∀ p, Algebra (A p) (K p)]
variable [∀ p, Algebra ℚ (K p)] [∀ p, Algebra (C p) (K p)]
variable [∀ p, IsScalarTower (A p) ℚ (K p)]
variable [∀ p, IsScalarTower (A p) (C p) (K p)]
variable [∀ p, IsFractionRing (A p) ℚ] [∀ p, IsIntegrallyClosed (A p)]

/-- Pair the proved generic transport with the actual modular approximation.
The coefficient rings may depend on the reduction prime. -/
def progressionInputs_of_powered_slash (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (powered : PoweredProgressionInputs p (A p) (C p) (K p))
    (approximation : SptApproximationInput p hp5) : ProgressionInputs p hp5 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact ⟨powered.toProgressionTransportInput, approximation⟩

/-- Conditional noncanonical exclusion with generic transport derived from
powered slash and rational descent, and Hadamard derived from positive trace
realization. The remaining assumptions retain their full prime and
admissible-discriminant domains. [rolenManuscript, Theorem 1] -/
theorem noncanonical_exclusion_of_powered_slash
    (tv : CharacterIntervalInput)
    (ct : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → QSeries.ConstantTermInputs p)
    (powered : ∀ (p : ℕ), p.Prime → 5 ≤ p →
      PoweredProgressionInputs p (A p) (C p) (K p))
    (approximation : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p,
      SptApproximationInput p hp5)
    (geometry : RealizedCharacterObstructionInputFamily)
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) :
    ((24 * b : ℕ) : ZMod p) = 1 := by
  exact noncanonical_exclusion_of_realized_geometry tv ct
    (fun q hq hq5 => progressionInputs_of_powered_slash q hq hq5
      (powered q hq hq5) (approximation q hq hq5))
    geometry p b hp hp5 hb hspt

/-- Conditional classification with the generic transport and trace bounds
proved. Canonical necessity and all three Andrews congruences remain explicit;
the verified finite exclusions handle primes two and three.
[rolenManuscript, Corollary 1] -/
theorem simple_congruence_classification_of_powered_slash
    (tv : CharacterIntervalInput)
    (ct : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → QSeries.ConstantTermInputs p)
    (powered : ∀ (p : ℕ), p.Prime → 5 ≤ p →
      PoweredProgressionInputs p (A p) (C p) (K p))
    (approximation : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p,
      SptApproximationInput p hp5)
    (geometry : RealizedCharacterObstructionInputFamily)
    (canonical : CanonicalInputs)
    (p b : ℕ) (hp : p.Prime) (hb : b < p) :
    (∀ n : ℕ, p ∣ spt (p * n + b)) ↔
      (p = 5 ∧ b = 4) ∨ (p = 7 ∧ b = 5) ∨ (p = 13 ∧ b = 6) := by
  exact simple_congruence_classification_of_realized_geometry tv ct
    (fun q hq hq5 => progressionInputs_of_powered_slash q hq hq5
      (powered q hq hq5) (approximation q hq hq5))
    geometry canonical p b hp hb

/-- Noncanonical exclusion with the product constant terms derived from the
actual analytic Hecke/shadow rows, progression transport from powered slash,
and the trace bound from positive realization. The remaining analytic and
geometric inputs keep their full domains. [rolenManuscript, Theorem 1] -/
theorem noncanonical_exclusion_of_analytic_inputs
    (tv : CharacterIntervalInput)
    (hecke : QSeries.AnalyticHeckePairingInputs)
    (powered : ∀ (p : ℕ), p.Prime → 5 ≤ p →
      PoweredProgressionInputs p (A p) (C p) (K p))
    (approximation : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p,
      SptApproximationInput p hp5)
    (geometry : RealizedCharacterObstructionInputFamily)
    (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) :
    ((24 * b : ℕ) : ZMod p) = 1 := by
  exact noncanonical_exclusion_of_realized_geometry tv
    (fun q _ hq5 => hecke.toConstantTermInputs q hq5)
    (fun q hq hq5 => progressionInputs_of_powered_slash q hq hq5
      (powered q hq hq5) (approximation q hq hq5))
    geometry p b hp hp5 hb hspt

/-- Classification for all primes from analytic Hecke/shadow rows, powered
progression data and realized CM geometry. Canonical necessity and the three
Andrews congruences remain explicit. [rolenManuscript, Corollary 1] -/
theorem simple_congruence_classification_of_analytic_inputs
    (tv : CharacterIntervalInput)
    (hecke : QSeries.AnalyticHeckePairingInputs)
    (powered : ∀ (p : ℕ), p.Prime → 5 ≤ p →
      PoweredProgressionInputs p (A p) (C p) (K p))
    (approximation : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p,
      SptApproximationInput p hp5)
    (geometry : RealizedCharacterObstructionInputFamily)
    (canonical : CanonicalInputs)
    (p b : ℕ) (hp : p.Prime) (hb : b < p) :
    (∀ n : ℕ, p ∣ spt (p * n + b)) ↔
      (p = 5 ∧ b = 4) ∨ (p = 7 ∧ b = 5) ∨ (p = 13 ∧ b = 6) := by
  exact simple_congruence_classification_of_realized_geometry tv
    (fun q _ hq5 => hecke.toConstantTermInputs q hq5)
    (fun q hq hq5 => progressionInputs_of_powered_slash q hq hq5
      (powered q hq hq5) (approximation q hq hq5))
    geometry canonical p b hp hb

end SptClassification
