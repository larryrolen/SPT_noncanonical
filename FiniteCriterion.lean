/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow95744

/-!
# The finite constant-character square criterion

The block certificates cover the inclusive interval through `10^11`. Their
soundness converts the packed computations into a statement about Jacobi symbols
of arbitrary natural numbers, including composite numbers.
-/

public section

namespace SptClassification.Sieve

/-- Every block meeting the inclusive source interval has a checked certificate. -/
theorem source_blocks_checked (k : ℕ) (hk : k ≤ sieveLimit / sieveBlockWidth) :
    checkBlock (checkedBlockLength sieveBlockWidth sieveLimit k) (sieveBlockWidth * k) = true := by
  rw [last_sieve_block] at hk
  rw [← indexedBlockCheck_eq hk]
  exact blocks_below_95744 k (by omega)

/-- A constant nonzero character pattern in the finite range forces a square. -/
theorem finite_character_criterion {x : ℕ} (hx : x ≤ 10 ^ 11)
    (hcop : x.Coprime (6 * ∏ q ∈ discriminantPrimes, q))
    (hconstant : ∀ q ∈ discriminantPrimes, ∀ r ∈ discriminantPrimes,
      jacobiSym (x : ℤ) q = jacobiSym (x : ℤ) r) : IsSquare x := by
  exact character_sieve_of_blocks sieveBlockWidth sieveLimit (by decide)
    source_blocks_checked (by simpa only [sieveLimit_eq] using hx) hcop hconstant

end SptClassification.Sieve
