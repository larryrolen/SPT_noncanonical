/- Assembled by AxiomProver. -/

module

public import SptClassification.QSeries.PrincipalFormsModPairing

/-!
# Conditional square coefficients of the principal forms

The two fields below are the finite constant terms of the actual Hecke
translates paired with the prescribed principal forms. They are the analytic
inputs to the coefficient argument of [rolenManuscript, §3, Lemma 3.1].
Their quantifiers are independent of a quadratic-character class.
-/

@[expose] public section

namespace SptClassification.QSeries

/-- Vanishing of both finite weight-two product constant terms for every
admissible principal part and every positive Hecke index prime to `6 * p`.
The prime-factor list retains multiplicities. The second product uses the
integral normalization `n² (P|Uₙ)` modulo `p`. -/
structure ConstantTermInputs (p : ℕ) [Fact p.Prime] where
  hPairing : ∀ d n : ℕ, d % 24 = 23 → 0 < n → n.Coprime (6 * p) →
    finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
      (fun r => (heckeThreeHalfWordInt n.primeFactorsList fFourier r : ZMod p))
      (fun r => (principalHFourier d (fFourier d) r : ZMod p)) = 0
  kPairing : ∀ d n : ℕ, d % 24 = 23 → 0 < n → n.Coprime (6 * p) →
    finiteConstantTerm (constantTermIndices n.primeFactorsList.prod d)
      (fun r => (n.primeFactorsList.prod : ZMod p) ^ 2 *
        heckeMinusHalfWordMod p n.primeFactorsList
          (fun s => (partitionFourier s : ZMod p)) r)
      (fun r => (principalKFourier d r : ZMod p)) = 0

/-- The prescribed square-index coefficients satisfy the manuscript relation
in the residue field, conditional on the two genuine finite pairings.
Divisor indices remain admissible because coprimality is inherited by divisors.
[rolenManuscript, §3, Lemma 3.1] -/
theorem conditional_square_coefficient_relation_mod
    (p : ℕ) [Fact p.Prime] (_hp : 5 ≤ p) (sign : ℤ)
    (_hsign : sign = 1 ∨ sign = -1) (d : ℕ) (_hdPos : 0 < d)
    (hd : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0)
    (hCT : ConstantTermInputs p) (m : ℕ) (hmPos : 0 < m)
    (hmCop : m.Coprime (6 * p)) :
    (m : ZMod p) ^ 2 *
      (principalHFourier d (fFourier d) ((m : ℤ) ^ 2) : ZMod p) +
      (d : ZMod p) * (principalKFourier d ((m : ℤ) ^ 2) : ZMod p) = 0 := by
  have hmCopP : m.Coprime p :=
    Nat.Coprime.of_dvd_right (⟨6, by omega⟩ : p ∣ 6 * p) hmCop
  have hmUnit : (m : ZMod p) ≠ 0 := by
    intro hmZero
    have hpm : ¬ p ∣ m :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd).mp hmCopP.symm
    exact hpm ((ZMod.natCast_eq_zero_iff m p).mp hmZero)
  exact principalForms_squareCoefficient_mod_of_constantTerms_zero
    p m d hmPos hmUnit hd sign hr hspt
    (fun n hnDvd hnPos => hCT.hPairing d n hd hnPos
      (Nat.Coprime.of_dvd_left hnDvd hmCop))
    (fun n hnDvd hnPos => hCT.kPairing d n hd hnPos
      (Nat.Coprime.of_dvd_left hnDvd hmCop))

/-- The conditional form of the manuscript's square-coefficient congruence,
for the actual partition-based `spt` and prescribed integral `H_d`, `K_d`
rows. [rolenManuscript, §3, Lemma 3.1] -/
theorem conditional_square_coefficient_relation
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) (d : ℕ) (hdPos : 0 < d)
    (hd : d % 24 = 23)
    (hr : legendreSym p (-(d : ℤ)) = sign)
    (hspt : ∀ j : ℕ, legendreSym p (1 - 24 * (j : ℤ)) = sign →
      ((spt j : ℤ) : ZMod p) = 0)
    (hCT : ConstantTermInputs p) (m : ℕ) (hmPos : 0 < m)
    (hmCop : m.Coprime (6 * p)) :
    (p : ℤ) ∣ (m : ℤ) ^ 2 *
      principalHFourier d (fFourier d) ((m : ℤ) ^ 2) +
      (d : ℤ) * principalKFourier d ((m : ℤ) ^ 2) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast] using
    conditional_square_coefficient_relation_mod p hp sign hsign d hdPos hd hr hspt
      hCT m hmPos hmCop

end SptClassification.QSeries
