/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks82944To84992
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow82944

/-! # Cumulative checker certificate through block 84991 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 84992 passes the packed checker. -/
public theorem blocks_below_84992 : ∀ k : ℕ, k < 84992 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 82944 2048 blocks_below_82944 blocks_in_82944_84992

end SptClassification.Sieve
