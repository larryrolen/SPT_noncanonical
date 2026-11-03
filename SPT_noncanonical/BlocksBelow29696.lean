/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks27648To29696
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow27648

/-! # Cumulative checker certificate through block 29695 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 29696 passes the packed checker. -/
public theorem blocks_below_29696 : ∀ k : ℕ, k < 29696 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 27648 2048 blocks_below_27648 blocks_in_27648_29696

end SptClassification.Sieve
