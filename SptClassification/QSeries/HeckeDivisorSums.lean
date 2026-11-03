/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.HeckeDivisorInduction

/-!
# From constant-term pairings to Hecke divisor sums

The two constant-term identities in [rolen2026canonical], Section 3, use
different normalizations of the same negative-square principal part. This
module clears their divisor-square denominators and combines them with the
coefficient congruence. The vanishing of the analytic constant terms is a
separate input to these algebraic results.
-/

public section

namespace SptClassification.QSeries

/-- Combine the two coefficient identities and the Hecke reduction. The
normalization `c t / t²` is defined because each index in the finite sum is
a unit in the coefficient field. -/
theorem heckeDivisorSum_of_pairingIdentities {F : Type*} [Field F]
    (I : Finset ℕ) (c : ℕ → F) (d A C : F) (h k : ℕ → F)
    (hUnit : ∀ t ∈ I, (t : F) ≠ 0)
    (hFirst : A + ∑ t ∈ I, c t * h t = 0)
    (hSecond : C + ∑ t ∈ I, c t / (t : F) ^ 2 * k t = 0)
    (hReduction : A = -d * C) :
    ∑ t ∈ I, c t / (t : F) ^ 2 * ((t : F) ^ 2 * h t + d * k t) = 0 := by
  have hTerms :
      (∑ t ∈ I, c t / (t : F) ^ 2 * ((t : F) ^ 2 * h t + d * k t)) =
        (∑ t ∈ I, c t * h t) +
          d * (∑ t ∈ I, c t / (t : F) ^ 2 * k t) := by
    calc
      _ = ∑ t ∈ I, (c t * h t + d * (c t / (t : F) ^ 2 * k t)) := by
        apply Finset.sum_congr rfl
        intro t ht
        have htUnit := hUnit t ht
        field_simp
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hTerms]
  linear_combination hFirst + d * hSecond - hReduction

/-- A vanishing constant-term pair for every divisor of `m`, together with
the character-class coefficient reduction, gives the manuscript's final
square-coefficient combination. The pairings remain explicit hypotheses. -/
theorem heckeSquareCombination_of_pairingIdentities {F : Type*} [Field F]
    (m : ℕ) (hm : 0 < m) (hmUnit : (m : F) ≠ 0)
    (d : F) (h k : ℕ → F)
    (A C : ℕ → F)
    (hFirst : ∀ n : ℕ, n ∣ m → 0 < n →
      A n + ∑ t ∈ n.divisors,
        ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : F) * h t = 0)
    (hSecond : ∀ n : ℕ, n ∣ m → 0 < n →
      C n + ∑ t ∈ n.divisors,
        ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : F) /
          (t : F) ^ 2 * k t = 0)
    (hReduction : ∀ n : ℕ, n ∣ m → 0 < n → A n = -d * C n) :
    (m : F) ^ 2 * h m + d * k m = 0 := by
  apply heckeSquareCombination_of_divisorSums m hm hmUnit d h k
  intro n hnDvd hnPos
  apply heckeDivisorSum_of_pairingIdentities n.divisors
    (fun t => ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : F))
    d (A n) (C n) h k
  · intro t ht
    have htDvd : t ∣ n := (Nat.mem_divisors.mp ht).1
    obtain ⟨u, hu⟩ := dvd_trans htDvd hnDvd
    intro htZero
    apply hmUnit
    calc
      (m : F) = (t : F) * (u : F) := by rw [hu, Nat.cast_mul]
      _ = 0 := by rw [htZero, zero_mul]
  · exact hFirst n hnDvd hnPos
  · exact hSecond n hnDvd hnPos
  · exact hReduction n hnDvd hnPos

end SptClassification.QSeries
