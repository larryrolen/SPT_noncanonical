/- Assembled by AxiomProver. -/

module

public import SptClassification.Classification.ConditionalCanonical
public import SptClassification.Classification.NoncanonicalExclusion

/-! # Classification of simple smallest-parts congruences -/

public section

namespace SptClassification

/-- The complete prime-modulus classification, including primes two and three.
This is the original unconditional target [rolenManuscript,
Corollary 1, label cor:classification]. The manuscript's noncanonical
theorem and the four named canonical-literature results are explicit
dependency leaves. -/
theorem simple_congruence_classification (p b : ℕ) (hp : p.Prime) (hb : b < p) :
    (∀ n : ℕ, p ∣ spt (p * n + b)) ↔
      (p = 5 ∧ b = 4) ∨ (p = 7 ∧ b = 5) ∨ (p = 13 ∧ b = 6) := by
  exact simple_congruence_classification_of_noncanonical_exclusion
    canonicalLiteratureInputs noncanonical_exclusion p b hp hb

end SptClassification
