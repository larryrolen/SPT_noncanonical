/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.FiniteReduction
public import SptClassification.Arithmetic.Sieve.FiniteCriterion

/-! # Smallest-parts character witnesses throughout the finite prime range -/

public section

namespace SptClassification

/-- Every prime from five through `10^11` has a nonzero smallest-parts coefficient
of each nonzero discriminant character, at an index at most eighty-seven. -/
theorem finite_class_witnesses (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hpB : p ≤ 10 ^ 11)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1) :
    ∃ N : ℕ, 1 ≤ N ∧ N ≤ 87 ∧ ¬p ∣ spt N ∧
      legendreSym p (1 - 24 * (N : ℤ)) = sign := by
  exact finite_class_witnesses_of_sieve (10 ^ 11)
    (fun _ _ hx hcop hconstant => Sieve.finite_character_criterion hx hcop hconstant)
    p hp hpB hsign

end SptClassification
