/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks19456To21504
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow19456

/-! # Cumulative checker certificate through block 21503 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 21504 passes the packed checker. -/
public theorem blocks_below_21504 : ∀ k : ℕ, k < 21504 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 19456 2048 blocks_below_19456 blocks_in_19456_21504

end SptClassification.Sieve
