/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks62464To64512
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow62464

/-! # Cumulative checker certificate through block 64511 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 64512 passes the packed checker. -/
public theorem blocks_below_64512 : ∀ k : ℕ, k < 64512 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 62464 2048 blocks_below_62464 blocks_in_62464_64512

end SptClassification.Sieve
