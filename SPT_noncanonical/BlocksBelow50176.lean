/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks48128To50176
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow48128

/-! # Cumulative checker certificate through block 50175 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 50176 passes the packed checker. -/
public theorem blocks_below_50176 : ∀ k : ℕ, k < 50176 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 48128 2048 blocks_below_48128 blocks_in_48128_50176

end SptClassification.Sieve
