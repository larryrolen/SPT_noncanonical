/- Assembled by AxiomProver. -/

module

public import SptClassification.Partitions.SmallestPartsTable
public import SptClassification.Arithmetic.FiniteWitnesses
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# The exact exceptional-prime set

The discriminant primes and the complete factorization of their smallest-parts
coefficient product are checked explicitly. Unique factorization identifies the
actual exceptional-prime set with the moduli in the small-witness certificate.
No factorization of the enormous product is performed by trial division.
-/

public section

namespace SptClassification

open QSeries

/-- The primes at most 2087 that are 23 modulo 24, given by their checked enumeration. -/
@[expose]
def discriminantPrimes : Finset ℕ :=
  {23,47,71,167,191,239,263,311,359,383,431,479,503,599,647,719,743,839,
   863,887,911,983,1031,1103,1151,1223,1319,1367,1439,1487,1511,1559,
   1583,1607,1823,1847,1871,2039,2063,2087}

private theorem discriminantPrimes_sound :
    ∀ q ∈ discriminantPrimes, q.Prime ∧ q ≤ 2087 ∧ q % 24 = 23 := by
  decide +kernel

private theorem discriminantPrimes_complete :
    ∀ k : Fin 87, (24 * k.val + 23).Prime →
      24 * k.val + 23 ∈ discriminantPrimes := by
  decide +kernel

/-- The enumeration is exactly the source's prime-and-residue predicate. -/
theorem mem_discriminantPrimes {q : ℕ} :
    q ∈ discriminantPrimes ↔ q.Prime ∧ q ≤ 2087 ∧ q % 24 = 23 := by
  constructor
  · exact discriminantPrimes_sound q
  · rintro ⟨hprime, hbound, hmod⟩
    have hkbound : q / 24 ≤ 86 := by omega
    have hrepr : q = 24 * (q / 24) + 23 := by omega
    have hprime' : (24 * (q / 24) + 23).Prime := by
      simpa only [← hrepr] using hprime
    have hmem := discriminantPrimes_complete ⟨q / 24, by omega⟩ hprime'
    simpa only [Fin.val_mk, ← hrepr] using hmem

theorem discriminantPrimes_card : discriminantPrimes.card = 40 := by
  decide +kernel

/-- The actual product whose prime divisors form the exceptional set. -/
noncomputable def sptWitnessProduct : ℕ :=
  ∏ q ∈ discriminantPrimes, q * spt ((q + 1) / 24)

/-- The product of the selected discriminants and their smallest-parts coefficients. -/
theorem sptWitnessProduct_eq_prod :
    sptWitnessProduct = ∏ q ∈ discriminantPrimes, q * spt ((q + 1) / 24) := by
  rfl

/-- The same product evaluated using the proved finite coefficient list. -/
def sptWitnessProductCandidate : ℕ :=
  ∏ q ∈ discriminantPrimes, q * (sptCoefficientValues[(q + 1) / 24]?).getD 0

theorem sptWitnessProduct_eq_candidate : sptWitnessProduct = sptWitnessProductCandidate := by
  unfold sptWitnessProduct sptWitnessProductCandidate
  apply Finset.prod_congr rfl
  intro q hq
  have hbound := (mem_discriminantPrimes.mp hq).2.1
  rw [spt_eq_coefficientValues (by omega)]

private def sptWitnessPrimeFactorsSmall : List ℕ :=
  List.replicate 22 3 ++ List.replicate 8 5 ++ List.replicate 11 7 ++ List.replicate 5 11

private def sptWitnessPrimeFactorsChunk1 : List ℕ :=
  [13, 17, 17, 19, 19, 23, 23, 29, 31, 37, 41, 47, 53, 67, 67, 71]

private def sptWitnessPrimeFactorsChunk2 : List ℕ :=
  [71, 71, 71, 89, 137, 167, 167, 191, 191, 191, 239, 263, 281, 311, 359, 383]

private def sptWitnessPrimeFactorsChunk3 : List ℕ :=
  [431, 433, 479, 491, 503, 599, 601, 617, 647, 673, 719, 743, 839, 863, 887, 911]

private def sptWitnessPrimeFactorsChunk4 : List ℕ :=
  [983, 1031, 1103, 1151, 1223, 1319, 1367, 1439, 1487, 1511, 1523, 1531, 1543, 1559, 1583, 1607]

private def sptWitnessPrimeFactorsChunk5 : List ℕ :=
  [1823, 1847, 1871, 2039, 2063, 2087, 2399, 2633, 3331, 3929, 8167, 8263, 9187, 11171, 11813, 22777]

private def sptWitnessPrimeFactorsChunk6 : List ℕ :=
  [27809, 127207, 128413, 133439, 343667, 645803, 682729, 4404161, 10859551, 66079291, 258555197]

/-- A prime-factor certificate, with multiplicities, for the complete coefficient product. -/
def sptWitnessPrimeFactors : List ℕ :=
  sptWitnessPrimeFactorsSmall ++ sptWitnessPrimeFactorsChunk1 ++
    sptWitnessPrimeFactorsChunk2 ++
    sptWitnessPrimeFactorsChunk3 ++
    sptWitnessPrimeFactorsChunk4 ++
    sptWitnessPrimeFactorsChunk5 ++
    sptWitnessPrimeFactorsChunk6

/-- Multiplying the certified prime factors gives the computed product exactly. -/
theorem sptWitnessProductCandidate_factorization :
    sptWitnessPrimeFactors.prod = sptWitnessProductCandidate := by
  norm_num [sptWitnessPrimeFactors, sptWitnessPrimeFactorsSmall,
    sptWitnessPrimeFactorsChunk1, sptWitnessPrimeFactorsChunk2, sptWitnessPrimeFactorsChunk3, sptWitnessPrimeFactorsChunk4, sptWitnessPrimeFactorsChunk5, sptWitnessPrimeFactorsChunk6,
    sptWitnessProductCandidate, discriminantPrimes, sptCoefficientValues]

private theorem sptWitnessPrimeFactorsSmall_prime :
    ∀ p ∈ sptWitnessPrimeFactorsSmall, p.Prime := by
  norm_num [sptWitnessPrimeFactorsSmall]

private theorem sptWitnessPrimeFactorsChunk1_prime :
    ∀ p ∈ sptWitnessPrimeFactorsChunk1, p.Prime := by
  norm_num [sptWitnessPrimeFactorsChunk1]

private theorem sptWitnessPrimeFactorsChunk2_prime :
    ∀ p ∈ sptWitnessPrimeFactorsChunk2, p.Prime := by
  norm_num [sptWitnessPrimeFactorsChunk2]

private theorem sptWitnessPrimeFactorsChunk3_prime :
    ∀ p ∈ sptWitnessPrimeFactorsChunk3, p.Prime := by
  norm_num [sptWitnessPrimeFactorsChunk3]

private theorem sptWitnessPrimeFactorsChunk4_prime :
    ∀ p ∈ sptWitnessPrimeFactorsChunk4, p.Prime := by
  norm_num [sptWitnessPrimeFactorsChunk4]

private theorem sptWitnessPrimeFactorsChunk5_prime :
    ∀ p ∈ sptWitnessPrimeFactorsChunk5, p.Prime := by
  norm_num [sptWitnessPrimeFactorsChunk5]

private theorem sptWitnessPrimeFactorsChunk6_prime :
    ∀ p ∈ sptWitnessPrimeFactorsChunk6, p.Prime := by
  norm_num [sptWitnessPrimeFactorsChunk6]

/-- Every number in the factor certificate is prime. -/
theorem sptWitnessPrimeFactors_prime : ∀ p ∈ sptWitnessPrimeFactors, p.Prime := by
  intro p hp
  simp only [sptWitnessPrimeFactors, List.mem_append, or_assoc] at hp
  rcases hp with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · exact sptWitnessPrimeFactorsSmall_prime p h0
  · exact sptWitnessPrimeFactorsChunk1_prime p h1
  · exact sptWitnessPrimeFactorsChunk2_prime p h2
  · exact sptWitnessPrimeFactorsChunk3_prime p h3
  · exact sptWitnessPrimeFactorsChunk4_prime p h4
  · exact sptWitnessPrimeFactorsChunk5_prime p h5
  · exact sptWitnessPrimeFactorsChunk6_prime p h6

theorem sptWitnessPrimeFactors_prod : sptWitnessPrimeFactors.prod = sptWitnessProduct := by
  rw [sptWitnessProduct_eq_candidate, sptWitnessProductCandidate_factorization]

/-- Unique factorization makes the factor certificate complete for the actual product. -/
theorem sptWitnessProduct_primeFactors :
    sptWitnessProduct.primeFactors = sptWitnessPrimeFactors.toFinset := by
  have hperm := Nat.primeFactorsList_unique sptWitnessPrimeFactors_prod sptWitnessPrimeFactors_prime
  rw [← Nat.toFinset_factors]
  ext p
  simp only [List.mem_toFinset]
  exact hperm.mem_iff.symm

/-- The primes at least five dividing the actual coefficient product. -/
noncomputable def exceptionalPrimes : Finset ℕ :=
  sptWitnessProduct.primeFactors.filter fun p => 5 ≤ p

/-- Membership in the exceptional set is divisibility by a prime at least five. -/
theorem mem_exceptionalPrimes_iff {p : ℕ} :
    p ∈ exceptionalPrimes ↔ p ∈ sptWitnessProduct.primeFactors ∧ 5 ≤ p := by
  simp only [exceptionalPrimes, Finset.mem_filter]

theorem prime_of_mem_exceptionalPrimes {p : ℕ} (hp : p ∈ exceptionalPrimes) : p.Prime :=
  (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1

/-- The explicit small-witness rows cover exactly the source's exceptional-prime set. -/
theorem exceptionalPrimes_eq_certificate :
    exceptionalPrimes = (smallWitnessCertificate.map Prod.fst).toFinset := by
  rw [exceptionalPrimes, sptWitnessProduct_primeFactors]
  decide +kernel

theorem exceptionalPrimes_card : exceptionalPrimes.card = 84 := by
  rw [exceptionalPrimes_eq_certificate]
  simpa only [List.toFinset_card_of_nodup, smallWitnessCertificate_moduli_nodup,
    List.length_map] using smallWitnessCertificate_length

/-- Every exceptional prime has a genuine smallest-parts witness in either nonzero class. -/
theorem exists_small_witness_of_exceptional (p : ℕ) [Fact p.Prime]
    (hp : p ∈ exceptionalPrimes) {sign : ℤ} (hsign : sign = 1 ∨ sign = -1) :
    ∃ N : ℕ, 1 ≤ N ∧ N ≤ 8 ∧ ¬p ∣ spt N ∧ legendreSym p (1 - 24 * (N : ℤ)) = sign := by
  rw [exceptionalPrimes_eq_certificate] at hp
  obtain ⟨⟨q, a, b⟩, hrow, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
  change q = p at heq
  subst q
  exact exists_small_witness_of_certificate p hrow hsign

end SptClassification
