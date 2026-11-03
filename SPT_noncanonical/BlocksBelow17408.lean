/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks15360To17408
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow15360

/-! # Cumulative checker certificate through block 17407 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 17408 passes the packed checker. -/
public theorem blocks_below_17408 : ∀ k : ℕ, k < 17408 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 15360 2048 blocks_below_15360 blocks_in_15360_17408

end SptClassification.Sieve
