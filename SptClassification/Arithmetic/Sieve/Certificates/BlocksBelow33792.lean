/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks31744To33792
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow31744

/-! # Cumulative checker certificate through block 33791 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 33792 passes the packed checker. -/
public theorem blocks_below_33792 : ∀ k : ℕ, k < 33792 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 31744 2048 blocks_below_31744 blocks_in_31744_33792

end SptClassification.Sieve
