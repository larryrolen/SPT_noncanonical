/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks23552To25600
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow23552

/-! # Cumulative checker certificate through block 25599 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 25600 passes the packed checker. -/
public theorem blocks_below_25600 : ∀ k : ℕ, k < 25600 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 23552 2048 blocks_below_23552 blocks_in_23552_25600

end SptClassification.Sieve
