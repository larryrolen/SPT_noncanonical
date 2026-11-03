/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks72704To74752
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow72704

/-! # Cumulative checker certificate through block 74751 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 74752 passes the packed checker. -/
public theorem blocks_below_74752 : ∀ k : ℕ, k < 74752 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 72704 2048 blocks_below_72704 blocks_in_72704_74752

end SptClassification.Sieve
