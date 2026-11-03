/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks60416To62464
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow60416

/-! # Cumulative checker certificate through block 62463 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 62464 passes the packed checker. -/
public theorem blocks_below_62464 : ∀ k : ℕ, k < 62464 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 60416 2048 blocks_below_60416 blocks_in_60416_62464

end SptClassification.Sieve
