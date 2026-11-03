/- Assembled by AxiomProver. -/

module

public import SptClassification.Classification.ConditionalCanonical
public import SptClassification.Classification.ConditionalExclusion

/-!
# Conditional classification of simple smallest-parts congruences

The noncanonical implication uses the proved propagation, arithmetic
witness, and Hasse obstruction deductions. The independent canonical
necessity and Andrews congruences remain explicit literature inputs.
[rolenManuscript, Theorem 1 and Corollary 1]
-/

public section

namespace SptClassification

/-- Conditional classification for every prime, including two and three,
of the actual partition-based smallest-parts simple progressions. The
CT, TR/AP, CM/EO, LF/QX/HG, TV, CA and AN inputs are explicit; neither
noncanonical exclusion nor classification is assumed. [rolenManuscript,
Corollary 1] -/
theorem conditional_simple_congruence_classification
    (tv : CharacterIntervalInput)
    (ct : ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → QSeries.ConstantTermInputs p)
    (progression : ∀ (p : ℕ), p.Prime → ∀ hp5 : 5 ≤ p, ProgressionInputs p hp5)
    (geometry : CharacterObstructionInputFamily)
    (canonical : CanonicalInputs)
    (p b : ℕ) (hp : p.Prime) (hb : b < p) :
    (∀ n : ℕ, p ∣ spt (p * n + b)) ↔
      (p = 5 ∧ b = 4) ∨ (p = 7 ∧ b = 5) ∨ (p = 13 ∧ b = 6) := by
  apply simple_congruence_classification_of_noncanonical_exclusion canonical
    (fun q c hq hq5 hc hspt =>
      conditional_noncanonical_exclusion tv ct progression geometry
        q c hq hq5 hc hspt) p b hp hb

end SptClassification
