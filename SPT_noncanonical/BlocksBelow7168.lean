/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks5120To7168
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow5120

/-! # Cumulative checker certificate through block 7167 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 7168 passes the packed checker. -/
public theorem blocks_below_7168 : ∀ k : ℕ, k < 7168 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 5120 2048 blocks_below_5120 blocks_in_5120_7168

end SptClassification.Sieve
