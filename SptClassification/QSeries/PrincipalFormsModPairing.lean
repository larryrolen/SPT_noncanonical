/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalFormsPairing
public import SptClassification.QSeries.HeckeMinusHalfMod

/-!
# Principal-form pairings modulo a prime

This is the coefficient reduction of the prescribed `H_d` and `K_d` rows
in [rolenManuscript, §3]. It retains the entire prime-factor word,
including repeated factors. Analytic vanishing of the weight-two product
constant terms is a separate premise.
-/

public section

namespace SptClassification.QSeries

/-- Agreement at negative input indices survives a square-index word. -/
theorem squareHeckeWord_eq_on_negative {K : Type*} [Semiring K]
    (ps : List ℕ) (hps : ∀ p ∈ ps, 0 < p)
    (middle : ℕ → ℤ → K) (last : ℕ → K)
    {A B : ℤ → K} (hAB : ∀ r : ℤ, r < 0 → A r = B r)
    {r : ℤ} (hr : r < 0) :
    squareHeckeWord middle last ps A r =
      squareHeckeWord middle last ps B r := by
  induction ps generalizing A B with
  | nil => simpa only [squareHeckeWord_nil] using hAB r hr
  | cons p ps ih =>
    have hp : 0 < p := hps p (by simp)
    have ht : ∀ q ∈ ps, 0 < q := fun q hq => hps q (by simp [hq])
    simpa only [squareHeckeWord_cons] using
      ih ht
        (fun s hs => squareHecke_eq_on_negative hp
          (middle p) (last p) hAB hs)

/-- On the negative principal part, the integral lift of the partition
derivative is the actual `f` Hecke word. -/
theorem scaledPartitionHecke_eq_fHecke_negative
    (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime)
    {r : ℤ} (hr : r < 0) :
    scaledPartitionHecke ps r = heckeThreeHalfWordInt ps fFourier r := by
  rw [scaledPartitionHecke_apply, heckeThreeHalfWordInt_eq_squareHeckeWord,
    heckeThreeHalfWordInt_eq_squareHeckeWord]
  exact (squareHeckeWord_eq_on_negative ps
    (fun p hp => (hps p hp).pos) etaHeckeDiagonalInt (fun p => (p : ℤ))
    (fun s hs => fFourier_negative hs) hr).symm

/-- The prescribed top negative coefficient of the reduced `H_d` row. -/
theorem principalHFourier_mod_neg_d (l d : ℕ) [Fact l.Prime]
    (hd : d % 24 = 23) :
    (principalHFourier d (fFourier d) (-(d : ℤ)) : ZMod l) = 1 := by
  have hdPos : 0 < d := by omega
  rw [principalHFourier_negative d hd _ _ (by omega)]
  simp

/-- The prescribed top negative coefficient of the reduced `K_d` row. -/
theorem principalKFourier_mod_neg_d (l d : ℕ) [Fact l.Prime]
    (hd : d % 24 = 23) :
    (principalKFourier d (-(d : ℤ)) : ZMod l) = 1 := by
  have hdPos : 0 < d := by omega
  rw [principalKFourier_negative d hd _ (by omega)]
  simp

/-- The first coefficient pairing, now in the residue field. -/
theorem principalH_hecke_finiteConstantTerm_mod (l : ℕ) [Fact l.Prime]
    (ps : List ℕ) (d : ℕ) (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices ps.prod d)
      (fun r => (heckeThreeHalfWordInt ps fFourier r : ZMod l))
      (fun r => (principalHFourier d (fFourier d) r : ZMod l)) =
      (heckeThreeHalfWordInt ps fFourier d : ZMod l) +
        ∑ t ∈ ps.prod.divisors,
          (heckePrincipalCoefficient ps t : ZMod l) *
            (principalHFourier d (fFourier d) ((t : ℤ) ^ 2) : ZMod l) := by
  have hdPos : 0 < d := by omega
  rw [finiteConstantTerm_divisorSquares hdPos,
    principalHFourier_mod_neg_d l d hd, mul_one]
  simp only [heckePrincipalCoefficient_apply]

/-- At a negative divisor square the reduced weight `-1/2` word has
coefficient `c_t/t²`. The unit premise is exactly what permits reduction
of this rational normalization modulo `l`. -/
theorem heckeMinusHalfWordMod_scaled_principalCoefficient
    (l : ℕ) [Fact l.Prime] (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime)
    (hpsUnit : ∀ p ∈ ps, (p : ZMod l) ≠ 0)
    (t : ℕ) (htPos : 0 < t) (htUnit : (t : ZMod l) ≠ 0) :
    (ps.prod : ZMod l) ^ 2 *
      heckeMinusHalfWordMod l ps
        (fun s => (partitionFourier s : ZMod l)) (- (t : ℤ) ^ 2) =
      (heckePrincipalCoefficient ps t : ZMod l) / (t : ZMod l) ^ 2 := by
  have hneg : - (t : ℤ) ^ 2 < 0 := by
    have htZ : (0 : ℤ) < t := by exact_mod_cast htPos
    nlinarith
  have hcoeff := scaledPartitionHecke_eq_fHecke_negative ps hps hneg
  have hmod := scaledPartitionHecke_mod_eq_minusHalfWord l ps hpsUnit
    (- (t : ℤ) ^ 2)
  rw [hcoeff] at hmod
  rw [← heckePrincipalCoefficient_apply] at hmod
  simp only [Int.cast_neg, Int.cast_pow, Int.cast_natCast, neg_neg] at hmod
  apply (eq_div_iff (pow_ne_zero 2 htUnit)).mpr
  calc
    _ = (t : ZMod l) ^ 2 *
        ((ps.prod : ZMod l) ^ 2 *
          heckeMinusHalfWordMod l ps
            (fun s => (partitionFourier s : ZMod l)) (- (t : ℤ) ^ 2)) := by ring
    _ = (heckePrincipalCoefficient ps t : ZMod l) := by
      simpa only [mul_assoc] using hmod.symm

/-- The second finite pairing with the prescribed `K_d` coefficients
after reduction modulo `l`. -/
theorem principalK_hecke_finiteConstantTerm_mod
    (l : ℕ) [Fact l.Prime] (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime)
    (hpsUnit : ∀ p ∈ ps, (p : ZMod l) ≠ 0)
    (hprodUnit : (ps.prod : ZMod l) ≠ 0)
    (d : ℕ) (hd : d % 24 = 23) :
    finiteConstantTerm (constantTermIndices ps.prod d)
      (fun r => (ps.prod : ZMod l) ^ 2 *
        heckeMinusHalfWordMod l ps
          (fun s => (partitionFourier s : ZMod l)) r)
      (fun r => (principalKFourier d r : ZMod l)) =
      (ps.prod : ZMod l) ^ 2 *
        heckeMinusHalfWordMod l ps
          (fun s => (partitionFourier s : ZMod l)) d +
        ∑ t ∈ ps.prod.divisors,
          (heckePrincipalCoefficient ps t : ZMod l) / (t : ZMod l) ^ 2 *
            (principalKFourier d ((t : ℤ) ^ 2) : ZMod l) := by
  have hdPos : 0 < d := by omega
  rw [finiteConstantTerm_divisorSquares hdPos,
    principalKFourier_mod_neg_d l d hd, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have hprodPos : 0 < ps.prod := by
    by_contra hnot
    have hz : ps.prod = 0 := by omega
    exact hprodUnit (by simp [hz])
  have htPos : 0 < t := Nat.pos_of_dvd_of_pos
    (Nat.mem_divisors.mp ht).1 hprodPos
  have htUnit : (t : ZMod l) ≠ 0 := by
    obtain ⟨u, hu⟩ := (Nat.mem_divisors.mp ht).1
    intro htZero
    apply hprodUnit
    calc
      (ps.prod : ZMod l) = (t : ZMod l) * (u : ZMod l) := by rw [hu, Nat.cast_mul]
      _ = 0 := by rw [htZero, zero_mul]
  rw [heckeMinusHalfWordMod_scaled_principalCoefficient l ps hps hpsUnit
    t htPos htUnit]

/-- The prescribed reduced `H_d` and `K_d` rows satisfy the divisor-square
coefficient relation when their weight-two product constant terms vanish.
The analytic vanishing remains an explicit premise. -/
theorem principalForms_squareCoefficient_mod_of_constantTerms_zero
    (l m d : ℕ) [Fact l.Prime]
    (hmPos : 0 < m) (hmUnit : (m : ZMod l) ≠ 0)
    (hd : d % 24 = 23) (sign : ℤ)
    (hr : legendreSym l (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym l (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod l) = 0)
    (hH : ∀ n : ℕ, n ∣ m → 0 < n →
      finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
        (fun r => (heckeThreeHalfWordInt n.primeFactorsList fFourier r : ZMod l))
        (fun r => (principalHFourier d (fFourier d) r : ZMod l)) = 0)
    (hK : ∀ n : ℕ, n ∣ m → 0 < n →
      finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
        (fun r => (n.primeFactorsList.prod : ZMod l) ^ 2 *
          heckeMinusHalfWordMod l n.primeFactorsList
            (fun s => (partitionFourier s : ZMod l)) r)
        (fun r => (principalKFourier d r : ZMod l)) = 0) :
    (m : ZMod l) ^ 2 *
      (principalHFourier d (fFourier d) ((m : ℤ) ^ 2) : ZMod l) +
      (d : ZMod l) * (principalKFourier d ((m : ℤ) ^ 2) : ZMod l) = 0 := by
  apply heckeSquareCombination_mod_of_actual_pairings l m d hmPos hmUnit
    sign hr hspt
    (fun t => (principalHFourier d (fFourier d) ((t : ℤ) ^ 2) : ZMod l))
    (fun t => (principalKFourier d ((t : ℤ) ^ 2) : ZMod l))
  · intro n hnDvd hnPos
    have hprod : n.primeFactorsList.prod = n :=
      Nat.prod_primeFactorsList (Nat.ne_of_gt hnPos)
    have hpair := principalH_hecke_finiteConstantTerm_mod l
      n.primeFactorsList d hd
    rw [hH n hnDvd hnPos, hprod] at hpair
    exact hpair.symm
  · intro n hnDvd hnPos
    have hprimes : ∀ p ∈ n.primeFactorsList, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactorsList hp
    have hunits : ∀ p ∈ n.primeFactorsList, (p : ZMod l) ≠ 0 := by
      intro p hp
      simpa only [Int.cast_natCast] using
        primeFactorsList_unit_of_dvd l m n hmUnit hnDvd hnPos p hp
    have hprod : n.primeFactorsList.prod = n :=
      Nat.prod_primeFactorsList (Nat.ne_of_gt hnPos)
    have hnUnit : (n.primeFactorsList.prod : ZMod l) ≠ 0 := by
      rw [hprod]
      obtain ⟨u, hu⟩ := hnDvd
      intro hnZero
      apply hmUnit
      simp [hu, hnZero]
    have hpair := principalK_hecke_finiteConstantTerm_mod l
      n.primeFactorsList hprimes hunits hnUnit d hd
    rw [hK n hnDvd hnPos, hprod] at hpair
    exact hpair.symm

end SptClassification.QSeries
