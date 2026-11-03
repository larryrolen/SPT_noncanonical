/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks70656To72704
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow70656

/-! # Cumulative checker certificate through block 72703 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 72704 passes the packed checker. -/
public theorem blocks_below_72704 : ∀ k : ℕ, k < 72704 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 70656 2048 blocks_below_70656 blocks_in_70656_72704

end SptClassification.Sieve
