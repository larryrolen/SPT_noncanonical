/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks13312To15360
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow13312

/-! # Cumulative checker certificate through block 15359 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 15360 passes the packed checker. -/
public theorem blocks_below_15360 : ∀ k : ℕ, k < 15360 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 13312 2048 blocks_below_13312 blocks_in_13312_15360

end SptClassification.Sieve
