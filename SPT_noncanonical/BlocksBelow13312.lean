/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks11264To13312
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow11264

/-! # Cumulative checker certificate through block 13311 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 13312 passes the packed checker. -/
public theorem blocks_below_13312 : ∀ k : ℕ, k < 13312 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 11264 2048 blocks_below_11264 blocks_in_11264_13312

end SptClassification.Sieve
