/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks54272To56320
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow54272

/-! # Cumulative checker certificate through block 56319 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 56320 passes the packed checker. -/
public theorem blocks_below_56320 : ∀ k : ℕ, k < 56320 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 54272 2048 blocks_below_54272 blocks_in_54272_56320

end SptClassification.Sieve
