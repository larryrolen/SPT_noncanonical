/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.ExceptionalPrimes
public import SptClassification.Arithmetic.SquareClasses
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Algebra.Prime.Lemmas

/-!
# Reduction of finite-range witnesses to a character-square criterion

Outside the exceptional set, the selected smallest-parts coefficients and
discriminant primes are units modulo the prime under consideration. Quadratic
reciprocity converts their discriminant characters into the finite character
test. The criterion that a constant character pattern forces a square then
supplies a witness for each sign.
-/

public section

namespace SptClassification

/-- Negative quadratic reciprocity when the positive discriminant is three modulo four. -/
theorem negative_jacobi_reciprocity {q l : ℕ} (hq : q % 4 = 3) (hl : Odd l) :
    jacobiSym (-(q : ℤ)) l = jacobiSym (l : ℤ) q := by
  have hqodd : Odd q := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.neg _ hl, ZMod.χ₄_nat_mod_four l]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hl) with h1 | h3
  · rw [h1]
    have hc : ZMod.χ₄ ((1 : ℕ) : ZMod 4) = 1 := by decide +kernel
    rw [hc, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hqodd h1]
  · rw [h3]
    have hc : ZMod.χ₄ ((3 : ℕ) : ZMod 4) = -1 := by decide +kernel
    rw [hc, jacobiSym.quadratic_reciprocity_three_mod_four hq h3]
    ring

theorem sptWitnessProduct_ne_zero : sptWitnessProduct ≠ 0 := by
  rw [← sptWitnessPrimeFactors_prod]
  intro hz
  have hmem : 0 ∈ sptWitnessPrimeFactors := List.prod_eq_zero_iff.mp hz
  exact (sptWitnessPrimeFactors_prime 0 hmem).ne_zero rfl

/-- Nonexceptional primes at least five do not divide the coefficient product. -/
theorem not_dvd_sptWitnessProduct (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hne : p ∉ exceptionalPrimes) : ¬p ∣ sptWitnessProduct := by
  intro hdiv
  apply hne
  exact mem_exceptionalPrimes_iff.mpr ⟨Nat.mem_primeFactors.mpr
    ⟨Fact.out, hdiv, sptWitnessProduct_ne_zero⟩, hp⟩

theorem discriminant_factor_dvd_product {q : ℕ} (hq : q ∈ discriminantPrimes) :
    q * spt ((q + 1) / 24) ∣ sptWitnessProduct := by
  rw [sptWitnessProduct_eq_prod]
  exact Finset.dvd_prod_of_mem (fun r => r * spt ((r + 1) / 24)) hq

theorem not_dvd_discriminant_of_nonexceptional (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hne : p ∉ exceptionalPrimes) {q : ℕ}
    (hq : q ∈ discriminantPrimes) : ¬p ∣ q := by
  intro hdiv
  apply not_dvd_sptWitnessProduct p hp hne
  exact (dvd_mul_of_dvd_left hdiv _).trans (discriminant_factor_dvd_product hq)

theorem not_dvd_spt_of_nonexceptional (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hne : p ∉ exceptionalPrimes) {q : ℕ}
    (hq : q ∈ discriminantPrimes) : ¬p ∣ spt ((q + 1) / 24) := by
  intro hdiv
  apply not_dvd_sptWitnessProduct p hp hne
  exact (dvd_mul_of_dvd_right hdiv _).trans (discriminant_factor_dvd_product hq)

/-- The two character conventions agree at each selected discriminant prime. -/
theorem discriminant_prime_reciprocity (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) {q : ℕ} (hq : q ∈ discriminantPrimes) :
    legendreSym p (-(q : ℤ)) = jacobiSym (p : ℤ) q := by
  rw [jacobiSym.legendreSym.to_jacobiSym]
  have hq4 : q % 4 = 3 := by
    have hq24 := (mem_discriminantPrimes.mp hq).2.2
    omega
  have hpodd : Odd p := Nat.odd_iff.mpr
    ((Nat.Prime.eq_two_or_odd (Fact.out : p.Prime)).resolve_left (by omega))
  exact negative_jacobi_reciprocity hq4 hpodd

theorem nonexceptional_character_values (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hne : p ∉ exceptionalPrimes) {q : ℕ}
    (hq : q ∈ discriminantPrimes) :
    jacobiSym (p : ℤ) q = 1 ∨ jacobiSym (p : ℤ) q = -1 := by
  have hnq : (q : ZMod p) ≠ 0 := by
    intro hz
    exact not_dvd_discriminant_of_nonexceptional p hp hne hq ((ZMod.natCast_eq_zero_iff q p).mp hz)
  have hneg : ((-(q : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    simpa only [Int.cast_neg, Int.cast_natCast, neg_ne_zero] using hnq
  simpa only [discriminant_prime_reciprocity p hp hq] using legendreSym.eq_one_or_neg_one p hneg

/-- Nonexceptional primes satisfy the coprimality input of the finite sieve. -/
theorem nonexceptional_coprime_sieve_modulus (p : ℕ) [Fact p.Prime]
    (hp : 5 ≤ p) (hne : p ∉ exceptionalPrimes) :
    p.Coprime (6 * ∏ q ∈ discriminantPrimes, q) := by
  have h6 : p.Coprime 6 := Nat.Coprime.of_dvd_right (by decide : 6 ∣ 24)
    (prime_coprime_twentyFour Fact.out hp)
  apply h6.mul_right
  apply Nat.Coprime.prod_right
  intro q hq
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    (not_dvd_discriminant_of_nonexceptional p hp hne hq)

/-- A character-square criterion supplies each sign among the selected primes. -/
theorem exists_discriminant_prime_of_sieve (B : ℕ)
    (hsieve : ∀ x : ℕ, 5 ≤ x → x ≤ B →
      x.Coprime (6 * ∏ q ∈ discriminantPrimes, q) →
      (∀ q ∈ discriminantPrimes, ∀ r ∈ discriminantPrimes,
        jacobiSym (x : ℤ) q = jacobiSym (x : ℤ) r) → IsSquare x)
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hpB : p ≤ B)
    (hne : p ∉ exceptionalPrimes) {sign : ℤ} (hsign : sign = 1 ∨ sign = -1) :
    ∃ q ∈ discriminantPrimes, jacobiSym (p : ℤ) q = sign := by
  classical
  by_contra! hnone
  have hopp : ∀ q ∈ discriminantPrimes, jacobiSym (p : ℤ) q = -sign := by
    intro q hq
    have hv := nonexceptional_character_values p hp hne hq
    rcases hsign with rfl | rfl
    · rcases hv with hv | hv
      · exact False.elim (hnone q hq hv)
      · exact hv
    · rcases hv with hv | hv
      · simpa using hv
      · exact False.elim (hnone q hq hv)
  have hconstant : ∀ q ∈ discriminantPrimes, ∀ r ∈ discriminantPrimes,
      jacobiSym (p : ℤ) q = jacobiSym (p : ℤ) r := by
    intro q hq r hr
    exact (hopp q hq).trans (hopp r hr).symm
  have hsquare := hsieve p hp hpB (nonexceptional_coprime_sieve_modulus p hp hne) hconstant
  exact (Nat.prime_iff.mp (Fact.out : p.Prime)).not_isSquare hsquare

/-- Together with the exceptional certificate, the sieve gives bounded spt witnesses. -/
theorem finite_class_witnesses_of_sieve (B : ℕ)
    (hsieve : ∀ x : ℕ, 5 ≤ x → x ≤ B →
      x.Coprime (6 * ∏ q ∈ discriminantPrimes, q) →
      (∀ q ∈ discriminantPrimes, ∀ r ∈ discriminantPrimes,
        jacobiSym (x : ℤ) q = jacobiSym (x : ℤ) r) → IsSquare x)
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hpB : p ≤ B)
    {sign : ℤ} (hsign : sign = 1 ∨ sign = -1) :
    ∃ N : ℕ, 1 ≤ N ∧ N ≤ 87 ∧ ¬p ∣ spt N ∧ legendreSym p (1 - 24 * (N : ℤ)) = sign := by
  by_cases he : p ∈ exceptionalPrimes
  · obtain ⟨N, hN, hN8, hunit, hchar⟩ := exists_small_witness_of_exceptional p he hsign
    exact ⟨N, hN, by omega, hunit, hchar⟩
  · obtain ⟨q, hq, hchar⟩ := exists_discriminant_prime_of_sieve B hsieve p hp hpB he hsign
    have hqdata := mem_discriminantPrimes.mp hq
    refine ⟨(q + 1) / 24, by omega, by omega,
      not_dvd_spt_of_nonexceptional p hp he hq, ?_⟩
    have hindex : (1 : ℤ) - 24 * (((q + 1) / 24 : ℕ) : ℤ) = -(q : ℤ) := by omega
    rw [hindex, discriminant_prime_reciprocity p hp hq]
    exact hchar

end SptClassification
