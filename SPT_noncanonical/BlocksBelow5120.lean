/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks3072To5120
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow3072

/-! # Cumulative checker certificate through block 5119 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 5120 passes the packed checker. -/
public theorem blocks_below_5120 : ∀ k : ℕ, k < 5120 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 3072 2048 blocks_below_3072 blocks_in_3072_5120

end SptClassification.Sieve
