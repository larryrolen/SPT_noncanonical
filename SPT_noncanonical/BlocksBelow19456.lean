/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks17408To19456
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow17408

/-! # Cumulative checker certificate through block 19455 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 19456 passes the packed checker. -/
public theorem blocks_below_19456 : ∀ k : ℕ, k < 19456 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 17408 2048 blocks_below_17408 blocks_in_17408_19456

end SptClassification.Sieve
