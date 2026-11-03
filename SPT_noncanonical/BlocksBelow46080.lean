/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks44032To46080
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow44032

/-! # Cumulative checker certificate through block 46079 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 46080 passes the packed checker. -/
public theorem blocks_below_46080 : ∀ k : ℕ, k < 46080 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 44032 2048 blocks_below_44032 blocks_in_44032_46080

end SptClassification.Sieve
