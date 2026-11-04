/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.HeckeDivisorSumsMod

/-!
# Integral reduction of the weight minus-one-half Hecke word

When every prime in a word is invertible modulo `l`, the weight `-1/2`
coefficient operator has its literal three-term formula over `ZMod l`.
The Euler derivative identity holds there without dividing by 24. It gives
an intrinsic reduction of the second coefficient in
[rolen2026canonical], Section 3, including repeated prime factors.
-/

@[expose] public section

namespace SptClassification.QSeries

/-- The negative Euler derivative on integral coefficient indices. -/
def negativeEuler {K : Type*} [Ring K] (A : ℤ → K) (r : ℤ) : K :=
  -(r : K) * A r

/-- The downward square shift intertwines the negative Euler derivative. -/
theorem squareDown_negativeEuler {K : Type*} [Field K]
    (p : ℕ) (A : ℤ → K) (r : ℤ) :
    (p : K) ^ 2 * squareDown p (negativeEuler A) r =
      -(r : K) * squareDown p A r := by
  simp only [squareDown_apply]
  split_ifs with hdiv
  · have hmul : r / (p : ℤ) ^ 2 * (p : ℤ) ^ 2 = r :=
      Int.ediv_mul_cancel hdiv
    have hcast : ((r / (p : ℤ) ^ 2 : ℤ) : K) * (p : K) ^ 2 = (r : K) := by
      have h := congrArg (fun z : ℤ => (z : K)) hmul
      simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using h
    dsimp [negativeEuler]
    calc
      (p : K) ^ 2 * (-((r / (p : ℤ) ^ 2 : ℤ) : K) * A (r / (p : ℤ) ^ 2)) =
          -( ((r / (p : ℤ) ^ 2 : ℤ) : K) * (p : K) ^ 2) *
            A (r / (p : ℤ) ^ 2) := by ring
      _ = _ := by rw [hcast]
  · simp

/-- The source's two three-term normalizations obey the derivative identity
over any field in which the Hecke prime is a unit. -/
theorem squareHecke_negativeEuler {K : Type*} [Field K]
    (p : ℕ) (hp : (p : K) ≠ 0) (middle : ℤ → K) (A : ℤ → K) :
    squareHecke p middle (p : K) (negativeEuler A) =
      fun r => (p : K) ^ 2 * negativeEuler
        (squareHecke p (fun s => middle s / (p : K) ^ 2)
          (1 / (p : K) ^ 3) A) r := by
  funext r
  have hdown : squareDown p (negativeEuler A) r =
      (-(r : K) * squareDown p A r) / (p : K) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 hp)).mpr
    simpa only [mul_comm] using squareDown_negativeEuler p A r
  simp only [squareHecke_apply, negativeEuler, hdown, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast]
  field_simp
  ring

/-- The weight `-1/2` word reduced to the prime field, with zero at
nonintegral downward indices inherited from `squareDown`. -/
def heckeMinusHalfWordMod (l : ℕ) [Fact l.Prime]
    (ps : List ℕ) (A : ℤ → ZMod l) :
    ℤ → ZMod l :=
  squareHeckeWord
    (fun p r => (etaHeckeDiagonalInt p r : ZMod l) / (p : ZMod l) ^ 2)
    (fun p => (1 : ZMod l) / (p : ZMod l) ^ 3) ps A

theorem heckeMinusHalfWordMod_eq_squareHeckeWord (l : ℕ) [Fact l.Prime]
    (ps : List ℕ) (A : ℤ → ZMod l) :
    heckeMinusHalfWordMod l ps A =
      squareHeckeWord
        (fun p r => (etaHeckeDiagonalInt p r : ZMod l) / (p : ZMod l) ^ 2)
        (fun p => (1 : ZMod l) / (p : ZMod l) ^ 3) ps A := (rfl)

/-- A constant coefficient factor commutes with any square-index word. -/
theorem squareHeckeWord_smul {K : Type*} [CommSemiring K]
    (middle : ℕ → ℤ → K) (last : ℕ → K)
    (ps : List ℕ) (c : K) (A : ℤ → K) :
    squareHeckeWord middle last ps (fun r => c * A r) =
      fun r => c * squareHeckeWord middle last ps A r := by
  induction ps generalizing A with
  | nil => simp only [squareHeckeWord_nil]
  | cons p ps ih =>
    have hstep : squareHecke p (middle p) (last p) (fun r => c * A r) =
        fun r => c * squareHecke p (middle p) (last p) A r := by
      funext r
      simp only [squareHecke_apply, squareDown_apply]
      split_ifs <;> ring
    simp only [squareHeckeWord_cons, hstep, ih]

/-- The repeated-prime word preserves the exact negative Euler derivative
relation over `ZMod l`. -/
theorem heckeWordMod_negativeEuler (l : ℕ) [Fact l.Prime] (ps : List ℕ)
    (hps : ∀ p ∈ ps, (p : ZMod l) ≠ 0) (A : ℤ → ZMod l) :
    squareHeckeWord
      (fun p r => (etaHeckeDiagonalInt p r : ZMod l))
      (fun p => (p : ZMod l)) ps (negativeEuler A) =
      fun r => (ps.prod : ZMod l) ^ 2 *
        negativeEuler (heckeMinusHalfWordMod l ps A) r := by
  induction ps generalizing A with
  | nil => simp [squareHeckeWord_nil, heckeMinusHalfWordMod]
  | cons p ps ih =>
    have hp : (p : ZMod l) ≠ 0 := hps p (by simp)
    have ht : ∀ q ∈ ps, (q : ZMod l) ≠ 0 :=
      fun q hq => hps q (by simp [hq])
    rw [squareHeckeWord_cons,
      squareHecke_negativeEuler (K := ZMod l) p hp
        (fun r => (etaHeckeDiagonalInt p r : ZMod l)) A]
    rw [squareHeckeWord_smul, ih ht]
    funext r
    simp only [heckeMinusHalfWordMod, squareHeckeWord_cons, List.prod_cons,
      Nat.cast_mul, mul_pow]
    ring

/-- The integer lift of the partition derivative is the actual reduced
weight `-1/2` word, scaled by the square of the word product. -/
theorem scaledPartitionHecke_mod_eq_minusHalfWord
    (l : ℕ) [Fact l.Prime] (ps : List ℕ)
    (hps : ∀ p ∈ ps, (p : ZMod l) ≠ 0) (r : ℤ) :
    (scaledPartitionHecke ps r : ZMod l) =
      -(r : ZMod l) * (ps.prod : ZMod l) ^ 2 *
        heckeMinusHalfWordMod l ps (fun s => (partitionFourier s : ZMod l)) r := by
  have hinput : (fun s : ℤ => ((-s * partitionFourier s : ℤ) : ZMod l)) =
      negativeEuler (fun s => (partitionFourier s : ZMod l)) := by
    funext s
    simp [negativeEuler]
  rw [scaledPartitionHecke_apply, heckeThreeHalfWordInt_mod]
  rw [hinput, heckeWordMod_negativeEuler l ps hps]
  simp only [negativeEuler]
  ring

/-- The square-coefficient combination follows from the two actual reduced
constant-term pairings. Their analytic vanishing is the remaining premise;
the derivative normalization and divisor induction are now proved here. -/
theorem heckeSquareCombination_mod_of_actual_pairings
    (l m d : ℕ) [Fact l.Prime]
    (hmPos : 0 < m) (hmUnit : (m : ZMod l) ≠ 0) (sign : ℤ)
    (hr : legendreSym l (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym l (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod l) = 0)
    (h k : ℕ → ZMod l)
    (hFirst : ∀ n : ℕ, n ∣ m → 0 < n →
      (heckeThreeHalfWordInt n.primeFactorsList fFourier (d : ℤ) : ZMod l) +
        ∑ t ∈ n.divisors,
          ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : ZMod l) * h t = 0)
    (hSecond : ∀ n : ℕ, n ∣ m → 0 < n →
      (n : ZMod l) ^ 2 *
        heckeMinusHalfWordMod l n.primeFactorsList
          (fun s => (partitionFourier s : ZMod l)) (d : ℤ) +
        ∑ t ∈ n.divisors,
          ((heckePrincipalCoefficient n.primeFactorsList t : ℤ) : ZMod l) /
            (t : ZMod l) ^ 2 * k t = 0) :
    (m : ZMod l) ^ 2 * h m + (d : ZMod l) * k m = 0 := by
  apply heckeSquareCombination_mod_of_pairings l m d hmPos hmUnit sign hr hspt
    h k (fun n => (n : ZMod l) ^ 2 *
      heckeMinusHalfWordMod l n.primeFactorsList
        (fun s => (partitionFourier s : ZMod l)) (d : ℤ))
  · exact hFirst
  · exact hSecond
  · intro n hnDvd hnPos
    have hword := scaledPartitionHecke_mod_eq_minusHalfWord l
      n.primeFactorsList
      (fun p hp => by
        simpa only [Int.cast_natCast] using
          primeFactorsList_unit_of_dvd l m n hmUnit hnDvd hnPos p hp)
      (d : ℤ)
    have hprod : n.primeFactorsList.prod = n :=
      Nat.prod_primeFactorsList (Nat.ne_of_gt hnPos)
    rw [hprod] at hword
    simpa only [Int.cast_natCast, mul_assoc] using hword

end SptClassification.QSeries
