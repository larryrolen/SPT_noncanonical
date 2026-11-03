/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.FiniteRange
public import SptClassification.Arithmetic.EffectiveCharacterDiscriminant
public import SptClassification.ModularForms.CongruencePropagation
public import SptClassification.ModularForms.CharacterObstruction

/-! # Exclusion of noncanonical smallest-parts congruences -/

public section

namespace SptClassification

/-- Every simple smallest-parts congruence at a prime at least five is canonical.
The finite coefficient witnesses exclude the small primes. For a large prime,
the corrected character-interval theorem supplies a discriminant to which the
geometric obstruction applies. [rolenManuscript, Theorem 1,
label thm:main] -/
theorem noncanonical_exclusion (p b : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hb : b < p) (hspt : ∀ n : ℕ, p ∣ spt (p * n + b)) :
    ((24 * b : ℕ) : ZMod p) = 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  by_contra hcanonical
  have hbnonzero : ((1 - 24 * (b : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro hz
    apply hcanonical
    calc
      ((24 * b : ℕ) : ZMod p) =
          1 - ((1 - 24 * (b : ℤ) : ℤ) : ZMod p) := by push_cast; ring
      _ = 1 := by rw [hz]; ring
  have hdiv : ¬(p : ℤ) ∣ 24 * (b : ℤ) - 1 := by
    intro hd
    apply hbnonzero
    have hz : ((24 * (b : ℤ) - 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    calc
      ((1 - 24 * (b : ℤ) : ℤ) : ZMod p) =
          -((24 * (b : ℤ) - 1 : ℤ) : ZMod p) := by push_cast; ring
      _ = 0 := by rw [hz]; ring
  let sign : ℤ := legendreSym p (1 - 24 * (b : ℤ))
  have hsign : sign = 1 ∨ sign = -1 :=
    legendreSym.eq_one_or_neg_one p hbnonzero
  have hclass : ∀ N : ℕ,
      legendreSym p (1 - 24 * (N : ℤ)) = sign → p ∣ spt N := by
    intro N hN
    exact propagation p b hp hp5 hb hspt hdiv N hN
  by_cases hsmall : p ≤ 10 ^ 11
  · obtain ⟨N, _, _, hnonzero, hN⟩ := finite_class_witnesses p hp5 hsmall hsign
    exact hnonzero (hclass N hN)
  · have hlarge : 10 ^ 11 ≤ p := by omega
    obtain ⟨d, hd, hdata⟩ := exists_large_prime_discriminant p hlarge hsign
    letI : Fact (-(d : ℤ) < 0) := ⟨by omega⟩
    obtain ⟨hmod, hsq, _, _, hvalue, hbound, hclassBound⟩ := hdata
    exact (character_obstruction p hp5 sign hsign d (by omega) hsq hmod
      hvalue hbound hclassBound) hclass

end SptClassification
