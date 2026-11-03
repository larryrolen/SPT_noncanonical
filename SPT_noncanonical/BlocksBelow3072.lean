/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks1024To3072
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow1024

/-! # Cumulative checker certificate through block 3071 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 3072 passes the packed checker. -/
public theorem blocks_below_3072 : ∀ k : ℕ, k < 3072 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 1024 2048 blocks_below_1024 blocks_in_1024_3072

end SptClassification.Sieve
