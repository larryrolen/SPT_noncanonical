/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalFormsModPairing

/-!
# Integral denominator clearing for the weight minus-one-half Hecke word

The weight `-1/2` operator in [rolenManuscript, §3] has denominators
`p²` and `p³`. Multiplying each prime step by `p³` gives an integral
coefficient operator. Its word is the bridge from rational constant-term
identities to their reduction modulo a prime away from the word product.
-/

public section

namespace SptClassification.QSeries

/-- The integral operator obtained by multiplying one weight `-1/2`
Hecke step by `p³`. The downward shift is zero at nonintegral indices. -/
def heckeMinusHalfClearedStep (p : ℕ) (A : ℤ → ℤ) (r : ℤ) : ℤ :=
  (p : ℤ) ^ 3 * A ((p : ℤ) ^ 2 * r) +
    (p : ℤ) * etaHeckeDiagonalInt p r * A r + squareDown p A r

/-- Integral denominator clearing for a full word, including repeated primes. -/
def heckeMinusHalfClearedWord : List ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | [], A => A
  | p :: ps, A => heckeMinusHalfClearedWord ps (heckeMinusHalfClearedStep p A)

/-- A prime step embeds in any field as `p³` times the literal rational-style
operator, provided `p` is invertible in that field. -/
theorem heckeMinusHalfClearedStep_cast {K : Type*} [Field K]
    (p : ℕ) (hp : (p : K) ≠ 0) (A : ℤ → ℤ) (r : ℤ) :
    (heckeMinusHalfClearedStep p A r : K) =
      (p : K) ^ 3 *
        squareHecke p
          (fun s => (etaHeckeDiagonalInt p s : K) / (p : K) ^ 2)
          (1 / (p : K) ^ 3) (fun s => (A s : K)) r := by
  simp only [heckeMinusHalfClearedStep, squareHecke_apply, Int.cast_add,
    Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  by_cases hdiv : (p : ℤ) ^ 2 ∣ r
  · simp [squareDown_apply, hdiv]; field_simp
  · simp [squareDown_apply, hdiv]; field_simp

/-- The integral cleared word embeds as the cube of the word product times
the weight `-1/2` word over any field in which the primes are units. -/
theorem heckeMinusHalfClearedWord_cast {K : Type*} [Field K]
    (ps : List ℕ) (hps : ∀ p ∈ ps, (p : K) ≠ 0)
    (A : ℤ → ℤ) (r : ℤ) :
    (heckeMinusHalfClearedWord ps A r : K) =
      (ps.prod : K) ^ 3 *
        squareHeckeWord
          (fun p s => (etaHeckeDiagonalInt p s : K) / (p : K) ^ 2)
          (fun p => (1 : K) / (p : K) ^ 3) ps
          (fun s => (A s : K)) r := by
  induction ps generalizing A with
  | nil => simp [heckeMinusHalfClearedWord, squareHeckeWord_nil]
  | cons p ps ih =>
    have hp : (p : K) ≠ 0 := hps p (by simp)
    have ht : ∀ q ∈ ps, (q : K) ≠ 0 := fun q hq => hps q (by simp [hq])
    rw [heckeMinusHalfClearedWord, ih ht]
    have hstep : (fun s : ℤ => (heckeMinusHalfClearedStep p A s : K)) =
        fun s => (p : K) ^ 3 *
          squareHecke p
            (fun t => (etaHeckeDiagonalInt p t : K) / (p : K) ^ 2)
            (1 / (p : K) ^ 3) (fun t => (A t : K)) s := by
      funext s
      exact heckeMinusHalfClearedStep_cast p hp A s
    rw [hstep, squareHeckeWord_smul]
    simp only [squareHeckeWord_cons, List.prod_cons, Nat.cast_mul, mul_pow]
    ring

/-- The integer cleared word is exactly the rational Hecke word with the
entire denominator `m³` cleared. -/
theorem heckeMinusHalfClearedWord_rat (ps : List ℕ)
    (hps : ∀ p ∈ ps, p ≠ 0) (A : ℤ → ℤ) (r : ℤ) :
    (heckeMinusHalfClearedWord ps A r : ℚ) =
      (ps.prod : ℚ) ^ 3 *
        heckeMinusHalfWord ps (fun s => (A s : ℚ)) r := by
  have hword (qs : List ℕ) (B : ℤ → ℚ) : heckeMinusHalfWord qs B =
      squareHeckeWord
        (fun p s => etaHeckeDiagonal p s / (p : ℚ) ^ 2)
        (fun p => (1 : ℚ) / (p : ℚ) ^ 3) qs B := by
    induction qs generalizing B with
    | nil => simp only [heckeMinusHalfWord_nil, squareHeckeWord_nil]
    | cons p ps ih =>
      simpa only [heckeMinusHalfWord_cons, squareHeckeWord_cons,
        heckeMinusHalf_eq_squareHecke] using
        ih (heckeMinusHalf p B)
  rw [hword ps]
  have hcast (p : ℕ) (s : ℤ) : (etaHeckeDiagonalInt p s : ℚ) =
      etaHeckeDiagonal p s := by
        simp [etaHeckeDiagonalInt_apply, etaHeckeDiagonal_apply]
  have hdiag :
      (fun (p : ℕ) (s : ℤ) => (etaHeckeDiagonalInt p s : ℚ) / (p : ℚ) ^ 2) =
        (fun p s => etaHeckeDiagonal p s / (p : ℚ) ^ 2) := by
    funext p s
    rw [hcast]
  have hsource := heckeMinusHalfClearedWord_cast (K := ℚ) ps
    (fun p hp => by norm_cast; exact hps p hp) A r
  rw [hdiag] at hsource
  exact hsource

/-- Reduction of the same integer word gives the literal weight `-1/2`
operator over `ZMod l`, scaled by the unit `m³`. -/
theorem heckeMinusHalfClearedWord_mod (l : ℕ) [Fact l.Prime]
    (ps : List ℕ) (hps : ∀ p ∈ ps, (p : ZMod l) ≠ 0)
    (A : ℤ → ℤ) (r : ℤ) :
    (heckeMinusHalfClearedWord ps A r : ZMod l) =
      (ps.prod : ZMod l) ^ 3 *
        heckeMinusHalfWordMod l ps (fun s => (A s : ZMod l)) r := by
  rw [heckeMinusHalfWordMod_eq_squareHeckeWord]
  exact heckeMinusHalfClearedWord_cast ps hps A r

/-- A rational zero constant-term pairing reduces to the literal finite-field
pairing when every prime denominator is invertible. The same integer Fourier
rows occur on both sides. -/
theorem heckeMinusHalf_finiteConstantTerm_mod_of_rat_zero
    (l : ℕ) [Fact l.Prime] (ps : List ℕ)
    (hps : ∀ p ∈ ps, p ≠ 0)
    (hpsUnit : ∀ p ∈ ps, (p : ZMod l) ≠ 0)
    (I : Finset ℤ) (A B : ℤ → ℤ)
    (hzero : finiteConstantTerm I
      (fun r => (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (A s : ℚ)) r)
      (fun r => (B r : ℚ)) = 0) :
    finiteConstantTerm I
      (fun r => (ps.prod : ZMod l) ^ 2 *
        heckeMinusHalfWordMod l ps (fun s => (A s : ZMod l)) r)
      (fun r => (B r : ZMod l)) = 0 := by
  let C : ℤ := finiteConstantTerm I (heckeMinusHalfClearedWord ps A) B
  have hrat : (C : ℚ) = (ps.prod : ℚ) *
      finiteConstantTerm I
        (fun r => (ps.prod : ℚ) ^ 2 *
          heckeMinusHalfWord ps (fun s => (A s : ℚ)) r)
        (fun r => (B r : ℚ)) := by
    simp only [C, finiteConstantTerm_apply, Int.cast_sum, Int.cast_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [heckeMinusHalfClearedWord_rat ps hps A r]
    ring
  have hC : C = 0 := by
    rw [hzero, mul_zero] at hrat
    exact_mod_cast hrat
  have hmod : (C : ZMod l) = (ps.prod : ZMod l) *
      finiteConstantTerm I
        (fun r => (ps.prod : ZMod l) ^ 2 *
          heckeMinusHalfWordMod l ps (fun s => (A s : ZMod l)) r)
        (fun r => (B r : ZMod l)) := by
    simp only [C, finiteConstantTerm_apply, Int.cast_sum, Int.cast_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [heckeMinusHalfClearedWord_mod l ps hpsUnit A r]
    ring
  have hprodUnit' (qs : List ℕ)
      (hqs : ∀ p ∈ qs, (p : ZMod l) ≠ 0) : (qs.prod : ZMod l) ≠ 0 := by
    induction qs with
    | nil => simp
    | cons p qs ih =>
      have hp : (p : ZMod l) ≠ 0 := hqs p (by simp)
      have ht : ∀ q ∈ qs, (q : ZMod l) ≠ 0 :=
        fun q hq => hqs q (by simp [hq])
      simpa only [List.prod_cons, Nat.cast_mul] using mul_ne_zero hp (ih ht)
  have hprodUnit : (ps.prod : ZMod l) ≠ 0 := hprodUnit' ps hpsUnit
  rw [hC, Int.cast_zero] at hmod
  exact (mul_eq_zero.mp hmod.symm).resolve_left hprodUnit

/-- The actual prescribed `K_d` row: rational vanishing of its weight-two
product coefficient supplies precisely the reduced pairing used in the
square-coefficient induction. -/
theorem principalK_finiteConstantTerm_mod_of_rat_zero
    (l : ℕ) [Fact l.Prime] (ps : List ℕ)
    (hps : ∀ p ∈ ps, p.Prime)
    (hpsUnit : ∀ p ∈ ps, (p : ZMod l) ≠ 0)
    (d : ℕ)
    (hzero : finiteConstantTerm (constantTermIndices ps.prod d)
      (fun r => (ps.prod : ℚ) ^ 2 *
        heckeMinusHalfWord ps (fun s => (partitionFourier s : ℚ)) r)
      (fun r => (principalKFourier d r : ℚ)) = 0) :
    finiteConstantTerm (constantTermIndices ps.prod d)
      (fun r => (ps.prod : ZMod l) ^ 2 *
        heckeMinusHalfWordMod l ps
          (fun s => (partitionFourier s : ZMod l)) r)
      (fun r => (principalKFourier d r : ZMod l)) = 0 := by
  exact heckeMinusHalf_finiteConstantTerm_mod_of_rat_zero l ps
    (fun p hp => (hps p hp).ne_zero) hpsUnit _ partitionFourier
    (principalKFourier d) hzero

/-- The integral weight `3/2` word carries a zero rational coefficient
pairing directly to every residue ring. -/
theorem heckeThreeHalf_finiteConstantTerm_mod_of_rat_zero
    (l : ℕ) (ps : List ℕ) (I : Finset ℤ) (A B : ℤ → ℤ)
    (hzero : finiteConstantTerm I
      (heckeThreeHalfWord ps (fun s => (A s : ℚ)))
      (fun r => (B r : ℚ)) = 0) :
    finiteConstantTerm I
      (fun r => (heckeThreeHalfWordInt ps A r : ZMod l))
      (fun r => (B r : ZMod l)) = 0 := by
  let C : ℤ := finiteConstantTerm I (heckeThreeHalfWordInt ps A) B
  have hrat : (C : ℚ) = finiteConstantTerm I
      (heckeThreeHalfWord ps (fun s => (A s : ℚ)))
      (fun r => (B r : ℚ)) := by
    simp only [C, finiteConstantTerm_apply, Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl
    intro r _
    rw [heckeThreeHalfWordInt_cast]
  have hC : C = 0 := by
    rw [hzero] at hrat
    exact_mod_cast hrat
  have hmod : (C : ZMod l) = finiteConstantTerm I
      (fun r => (heckeThreeHalfWordInt ps A r : ZMod l))
      (fun r => (B r : ZMod l)) := by
    simp only [C, finiteConstantTerm_apply, Int.cast_sum, Int.cast_mul]
  rw [hC, Int.cast_zero] at hmod
  exact hmod.symm

/-- The prescribed `H_d` rational pairing gives the residue-field pairing
without any denominator condition. -/
theorem principalH_finiteConstantTerm_mod_of_rat_zero
    (l : ℕ) [Fact l.Prime] (ps : List ℕ) (d : ℕ)
    (hzero : finiteConstantTerm (constantTermIndices ps.prod d)
      (heckeThreeHalfWord ps (fun s => (fFourier s : ℚ)))
      (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0) :
    finiteConstantTerm (constantTermIndices ps.prod d)
      (fun r => (heckeThreeHalfWordInt ps fFourier r : ZMod l))
      (fun r => (principalHFourier d (fFourier d) r : ZMod l)) = 0 := by
  exact heckeThreeHalf_finiteConstantTerm_mod_of_rat_zero l ps _ fFourier
    (principalHFourier d (fFourier d)) hzero

/-- Rational vanishing of the two actual H/K weight-two product
coefficients, for all divisors, supplies the exact modular premises of the
triangular square-coefficient argument. The analytic modularity and
constant-term theorem are still needed to prove those rational vanishing
premises. -/
theorem principalForms_squareCoefficient_mod_of_rat_constantTerms_zero
    (l m d : ℕ) [Fact l.Prime]
    (hmPos : 0 < m) (hmUnit : (m : ZMod l) ≠ 0)
    (hd : d % 24 = 23) (sign : ℤ)
    (hr : legendreSym l (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym l (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod l) = 0)
    (hH : ∀ n : ℕ, n ∣ m → 0 < n →
      finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
        (heckeThreeHalfWord n.primeFactorsList
          (fun r => (fFourier r : ℚ)))
        (fun r => (principalHFourier d (fFourier d) r : ℚ)) = 0)
    (hK : ∀ n : ℕ, n ∣ m → 0 < n →
      finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
        (fun r => (n.primeFactorsList.prod : ℚ) ^ 2 *
          heckeMinusHalfWord n.primeFactorsList
            (fun s => (partitionFourier s : ℚ)) r)
        (fun r => (principalKFourier d r : ℚ)) = 0) :
    (m : ZMod l) ^ 2 *
      (principalHFourier d (fFourier d) ((m : ℤ) ^ 2) : ZMod l) +
      (d : ZMod l) * (principalKFourier d ((m : ℤ) ^ 2) : ZMod l) = 0 := by
  apply principalForms_squareCoefficient_mod_of_constantTerms_zero
    l m d hmPos hmUnit hd sign hr hspt
  · intro n hnDvd hnPos
    exact principalH_finiteConstantTerm_mod_of_rat_zero l
      n.primeFactorsList d (hH n hnDvd hnPos)
  · intro n hnDvd hnPos
    have hprimes : ∀ p ∈ n.primeFactorsList, p.Prime :=
      fun p hp => Nat.prime_of_mem_primeFactorsList hp
    have hunits : ∀ p ∈ n.primeFactorsList, (p : ZMod l) ≠ 0 := by
      intro p hp
      simpa only [Int.cast_natCast] using
        primeFactorsList_unit_of_dvd l m n hmUnit hnDvd hnPos p hp
    exact principalK_finiteConstantTerm_mod_of_rat_zero l
      n.primeFactorsList hprimes hunits d (hK n hnDvd hnPos)

end SptClassification.QSeries
