/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks35840To37888
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow35840

/-! # Cumulative checker certificate through block 37887 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 37888 passes the packed checker. -/
public theorem blocks_below_37888 : ∀ k : ℕ, k < 37888 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 35840 2048 blocks_below_35840 blocks_in_35840_37888

end SptClassification.Sieve
