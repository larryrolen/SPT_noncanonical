/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.HeckeDivisorSums

/-!
# Hecke divisor sums on a quadratic-character class

The coefficient reduction for the actual repeated-prime word is combined with
the finite pairings from [rolen2026canonical], Section 3. The pairing equations
and the modular reduction of the second Hecke coefficient remain explicit
inputs until the analytic constant-term identities are available.
-/

public section

namespace SptClassification.QSeries

/-- Every prime in the factor list of a divisor of `m` is a unit modulo `l`
when `m` is a unit. This keeps repeated prime factors in the Hecke word. -/
theorem primeFactorsList_unit_of_dvd (l m n : ℕ) [Fact l.Prime]
    (hmUnit : (m : ZMod l) ≠ 0) (hnDvd : n ∣ m) (hnPos : 0 < n) :
    ∀ p ∈ n.primeFactorsList, ((p : ℤ) : ZMod l) ≠ 0 := by
  have hnUnit : (n : ZMod l) ≠ 0 := by
    obtain ⟨u, hu⟩ := hnDvd
    intro hnZero
    apply hmUnit
    calc
      (m : ZMod l) = (n : ZMod l) * (u : ZMod l) := by rw [hu, Nat.cast_mul]
      _ = 0 := by rw [hnZero, zero_mul]
  have hFactors (ps : List ℕ) (hprod : (ps.prod : ZMod l) ≠ 0) :
      ∀ p ∈ ps, (p : ZMod l) ≠ 0 := by
    induction ps with
    | nil => simp
    | cons q qs ih =>
      have hq : (q : ZMod l) ≠ 0 := by
        intro hzero
        apply hprod
        simp [List.prod_cons, hzero]
      have hqs : (qs.prod : ZMod l) ≠ 0 := by
        intro hzero
        apply hprod
        simp [List.prod_cons, hzero]
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hq
      · exact ih hqs p hp
  have hprod : n.primeFactorsList.prod = n :=
    Nat.prod_primeFactorsList (Nat.ne_of_gt hnPos)
  intro p hp
  have h := hFactors n.primeFactorsList (by simpa only [hprod] using hnUnit) p hp
  simpa only [Int.cast_natCast] using h

/-- The actual integral `f` Hecke word agrees modulo `l` with the integral
lift of the derivative of the partition Hecke word at every divisor of `m`. -/
theorem fHecke_mod_eq_scaledPartitionHecke_divisor
    (l m n : ℕ) [Fact l.Prime]
    (hmUnit : (m : ZMod l) ≠ 0) (hnDvd : n ∣ m) (hnPos : 0 < n)
    (sign : ℤ)
    (hspt : ∀ j : ℕ, legendreSym l (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod l) = 0)
    (r : ℤ) (hr : legendreSym l (-r) = sign) :
    (heckeThreeHalfWordInt n.primeFactorsList fFourier r : ZMod l) =
      (scaledPartitionHecke n.primeFactorsList r : ZMod l) := by
  exact fHecke_mod_eq_scaledPartitionHecke l sign n.primeFactorsList
    (primeFactorsList_unit_of_dvd l m n hmUnit hnDvd hnPos) hspt r hr

/-- The manuscript's final divisor induction after specializing the first
pairing to the actual `f` Hecke coefficients. `C` is the reduced second
coefficient; its scale equation records the integral derivative bridge. -/
theorem heckeSquareCombination_mod_of_pairings
    (l m d : ℕ) [Fact l.Prime]
    (hmPos : 0 < m) (hmUnit : (m : ZMod l) ≠ 0) (sign : ℤ)
    (hr : legendreSym l (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym l (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod l) = 0)
    (h k : ℕ → ZMod l) (C : ℕ → ZMod l)
    (hFirst : ∀ n : ℕ, n ∣ m → 0 < n →
      (heckeThreeHalfWordInt n.primeFactorsList fFourier (d : ℤ) : ZMod l) +
        ∑ t ∈ n.divisors,
          ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : ZMod l) * h t = 0)
    (hSecond : ∀ n : ℕ, n ∣ m → 0 < n →
      C n + ∑ t ∈ n.divisors,
        ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : ZMod l) /
          (t : ZMod l) ^ 2 * k t = 0)
    (hScale : ∀ n : ℕ, n ∣ m → 0 < n →
      (scaledPartitionHecke n.primeFactorsList (d : ℤ) : ZMod l) =
        -(d : ZMod l) * C n) :
    (m : ZMod l) ^ 2 * h m + (d : ZMod l) * k m = 0 := by
  apply heckeSquareCombination_of_pairingIdentities m hmPos hmUnit
    (d : ZMod l) h k
    (fun n => (heckeThreeHalfWordInt n.primeFactorsList fFourier (d : ℤ) : ZMod l)) C
  · exact hFirst
  · exact hSecond
  · intro n hnDvd hnPos
    calc
      (heckeThreeHalfWordInt n.primeFactorsList fFourier (d : ℤ) : ZMod l) =
          (scaledPartitionHecke n.primeFactorsList (d : ℤ) : ZMod l) :=
        fHecke_mod_eq_scaledPartitionHecke_divisor l m n hmUnit hnDvd hnPos
          sign hspt (d : ℤ) hr
      _ = _ := hScale n hnDvd hnPos

end SptClassification.QSeries
