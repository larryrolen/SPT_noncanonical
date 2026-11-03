/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks56320To58368
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow56320

/-! # Cumulative checker certificate through block 58367 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 58368 passes the packed checker. -/
public theorem blocks_below_58368 : ∀ k : ℕ, k < 58368 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 56320 2048 blocks_below_56320 blocks_in_56320_58368

end SptClassification.Sieve
