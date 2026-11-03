/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks37888To39936
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow37888

/-! # Cumulative checker certificate through block 39935 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 39936 passes the packed checker. -/
public theorem blocks_below_39936 : ∀ k : ℕ, k < 39936 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 37888 2048 blocks_below_37888 blocks_in_37888_39936

end SptClassification.Sieve
