/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks33792To35840
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow33792

/-! # Cumulative checker certificate through block 35839 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 35840 passes the packed checker. -/
public theorem blocks_below_35840 : ∀ k : ℕ, k < 35840 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 33792 2048 blocks_below_33792 blocks_in_33792_35840

end SptClassification.Sieve
