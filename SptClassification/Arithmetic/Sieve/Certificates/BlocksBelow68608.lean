/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks66560To68608
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow66560

/-! # Cumulative checker certificate through block 68607 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 68608 passes the packed checker. -/
public theorem blocks_below_68608 : ∀ k : ℕ, k < 68608 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 66560 2048 blocks_below_66560 blocks_in_66560_68608

end SptClassification.Sieve
