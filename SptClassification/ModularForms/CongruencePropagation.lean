/- Assembled by AxiomProver. -/

module

public import SptClassification.ModularForms.ActualTwistedApproximation

/-! # Propagation of a noncanonical smallest-parts congruence -/

public section

namespace SptClassification

/-- A noncanonical congruence propagates to its whole quadratic-character class.
The manuscript deduction [rolenManuscript, label lem:prop] uses the actual
normalized approximation and the named classical literature premises. -/
theorem propagation (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hb : b < p)
    (hspt : ∀ n : ℕ, p ∣ spt (p * n + b))
    (hnotcanonical : ¬(p : ℤ) ∣ 24 * (b : ℤ) - 1)
    (N : ℕ)
    (hclass : @legendreSym p ⟨hp⟩ (1 - 24 * (N : ℤ)) =
      @legendreSym p ⟨hp⟩ (1 - 24 * (b : ℤ))) :
    p ∣ spt N := by
  let : Fact p.Prime := ⟨hp⟩
  apply propagation_of_actual_cusp_law p b hp hp5 hb ?_ hspt ?_ N hclass
  · intro hzero
    exact hnotcanonical ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hzero)
  · intro Q hQ havoid
    have hodd : Odd Q := (Fact.out : Q.Prime).odd_of_ne_two (by
      intro htwo
      apply havoid
      rw [htwo]
      exact dvd_mul_of_dvd_left (by decide : 2 ∣ 6) p)
    exact sptTwistedAnalyticData_normalizedRepresentative_cusps hp5 hodd

end SptClassification
