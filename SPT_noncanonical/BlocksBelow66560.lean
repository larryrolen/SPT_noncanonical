/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks64512To66560
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow64512

/-! # Cumulative checker certificate through block 66559 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 66560 passes the packed checker. -/
public theorem blocks_below_66560 : ∀ k : ℕ, k < 66560 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 64512 2048 blocks_below_64512 blocks_in_64512_66560

end SptClassification.Sieve
