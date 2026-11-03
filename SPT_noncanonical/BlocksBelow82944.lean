/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks80896To82944
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow80896

/-! # Cumulative checker certificate through block 82943 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 82944 passes the packed checker. -/
public theorem blocks_below_82944 : ∀ k : ℕ, k < 82944 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 80896 2048 blocks_below_80896 blocks_in_80896_82944

end SptClassification.Sieve
