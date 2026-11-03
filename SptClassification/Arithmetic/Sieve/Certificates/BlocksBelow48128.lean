/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks46080To48128
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow46080

/-! # Cumulative checker certificate through block 48127 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 48128 passes the packed checker. -/
public theorem blocks_below_48128 : ∀ k : ℕ, k < 48128 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 46080 2048 blocks_below_46080 blocks_in_46080_48128

end SptClassification.Sieve
