/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks9216To11264
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow9216

/-! # Cumulative checker certificate through block 11263 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 11264 passes the packed checker. -/
public theorem blocks_below_11264 : ∀ k : ℕ, k < 11264 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 9216 2048 blocks_below_9216 blocks_in_9216_11264

end SptClassification.Sieve
