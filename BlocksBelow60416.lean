/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks58368To60416
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow58368

/-! # Cumulative checker certificate through block 60415 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 60416 passes the packed checker. -/
public theorem blocks_below_60416 : ∀ k : ℕ, k < 60416 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 58368 2048 blocks_below_58368 blocks_in_58368_60416

end SptClassification.Sieve
