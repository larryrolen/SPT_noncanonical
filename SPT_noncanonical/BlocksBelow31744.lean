/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks29696To31744
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow29696

/-! # Cumulative checker certificate through block 31743 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 31744 passes the packed checker. -/
public theorem blocks_below_31744 : ∀ k : ℕ, k < 31744 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 29696 2048 blocks_below_29696 blocks_in_29696_31744

end SptClassification.Sieve
