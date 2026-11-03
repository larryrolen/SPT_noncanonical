/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks39936To41984
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow39936

/-! # Cumulative checker certificate through block 41983 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 41984 passes the packed checker. -/
public theorem blocks_below_41984 : ∀ k : ℕ, k < 41984 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 39936 2048 blocks_below_39936 blocks_in_39936_41984

end SptClassification.Sieve
