/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks7168To9216
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow7168

/-! # Cumulative checker certificate through block 9215 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 9216 passes the packed checker. -/
public theorem blocks_below_9216 : ∀ k : ℕ, k < 9216 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 7168 2048 blocks_below_7168 blocks_in_7168_9216

end SptClassification.Sieve
