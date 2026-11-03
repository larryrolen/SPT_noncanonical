/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks21504To23552
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow21504

/-! # Cumulative checker certificate through block 23551 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 23552 passes the packed checker. -/
public theorem blocks_below_23552 : ∀ k : ℕ, k < 23552 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 21504 2048 blocks_below_21504 blocks_in_21504_23552

end SptClassification.Sieve
