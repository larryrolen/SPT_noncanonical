/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks89088To91136
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow89088

/-! # Cumulative checker certificate through block 91135 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 91136 passes the packed checker. -/
public theorem blocks_below_91136 : ∀ k : ℕ, k < 91136 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 89088 2048 blocks_below_89088 blocks_in_89088_91136

end SptClassification.Sieve
