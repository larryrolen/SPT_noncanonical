/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks68608To70656
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow68608

/-! # Cumulative checker certificate through block 70655 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 70656 passes the packed checker. -/
public theorem blocks_below_70656 : ∀ k : ℕ, k < 70656 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 68608 2048 blocks_below_68608 blocks_in_68608_70656

end SptClassification.Sieve
