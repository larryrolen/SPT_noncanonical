/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.ConstantTermPairing

/-!
# Induction on the triangular Hecke principal part

The final algebraic step of [rolen2026canonical], Lemma 3.1, uses the
coefficient at the largest divisor square to remove each term of a finite
divisor sum. The sum relation is supplied separately by the analytic
constant-term argument. Repeated prime factors remain in `primeFactorsList`.
-/

public section

namespace SptClassification.QSeries

/-- A family of vanishing divisor sums with the actual Hecke coefficients
forces the summand at every divisor of `m` to vanish. The condition that `m`
is nonzero in the field is the exact unit needed for the diagonal term. -/
theorem heckeDivisorSum_induction {F : Type*} [Field F]
    (m : ℕ) (hmUnit : (m : F) ≠ 0) (B : ℕ → F)
    (hSum : ∀ n : ℕ, n ∣ m → 0 < n →
      ∑ t ∈ n.divisors,
        ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : F) /
          (t : F) ^ 2 * B t = 0) :
    ∀ n : ℕ, n ∣ m → 0 < n → B n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnDvd hnPos
    have hprod : n.primeFactorsList.prod = n :=
      Nat.prod_primeFactorsList (Nat.ne_of_gt hnPos)
    have hprimes : ∀ p ∈ n.primeFactorsList, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactorsList hp
    have htop : heckePrincipalCoefficient n.primeFactorsList n = (n : ℤ) := by
      simpa only [hprod] using
        (heckePrincipalCoefficient_top n.primeFactorsList hprimes)
    have hnUnit : (n : F) ≠ 0 := by
      obtain ⟨u, hu⟩ := hnDvd
      intro hnZero
      apply hmUnit
      calc
        (m : F) = (n : F) * (u : F) := by rw [hu, Nat.cast_mul]
        _ = 0 := by rw [hnZero, zero_mul]
    have hnMem : n ∈ n.divisors :=
      Nat.mem_divisors.mpr ⟨dvd_refl n, Nat.ne_of_gt hnPos⟩
    have hSingle :
        (∑ t ∈ n.divisors,
          ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : F) /
            (t : F) ^ 2 * B t) =
          ((heckePrincipalCoefficient n.primeFactorsList n : ℤ) : F) /
            (n : F) ^ 2 * B n := by
      apply Finset.sum_eq_single n
      · intro t ht hne
        have htDvd : t ∣ n := (Nat.mem_divisors.mp ht).1
        have htPos : 0 < t := Nat.pos_of_dvd_of_pos htDvd hnPos
        have htLt : t < n := by
          have htLe := Nat.le_of_dvd hnPos htDvd
          omega
        rw [ih t htLt (dvd_trans htDvd hnDvd) htPos, mul_zero]
      · intro hnot
        exact False.elim (hnot hnMem)
    have hDiagonal : (n : F) / (n : F) ^ 2 ≠ 0 :=
      div_ne_zero hnUnit (pow_ne_zero 2 hnUnit)
    have h := hSum n hnDvd hnPos
    rw [hSingle, htop, Int.cast_natCast] at h
    exact (mul_eq_zero.mp h).resolve_left hDiagonal

/-- The square-coefficient combination in the manuscript vanishes once
its finite constant-term pairing is known at every divisor of `m`. This is
only the divisor induction; the analytic pairing is a separate premise. -/
theorem heckeSquareCombination_of_divisorSums {F : Type*} [Field F]
    (m : ℕ) (hm : 0 < m) (hmUnit : (m : F) ≠ 0)
    (d : F) (h k : ℕ → F)
    (hSum : ∀ n : ℕ, n ∣ m → 0 < n →
      ∑ t ∈ n.divisors,
        ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : F) /
          (t : F) ^ 2 * ((t : F) ^ 2 * h t + d * k t) = 0) :
    (m : F) ^ 2 * h m + d * k m = 0 := by
  exact heckeDivisorSum_induction m hmUnit
    (fun t => (t : F) ^ 2 * h t + d * k t) hSum m (dvd_refl m) hm

end SptClassification.QSeries
