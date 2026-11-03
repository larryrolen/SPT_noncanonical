/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks93184To95232
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow93184

/-! # Cumulative checker certificate through block 95231 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 95232 passes the packed checker. -/
public theorem blocks_below_95232 : ∀ k : ℕ, k < 95232 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 93184 2048 blocks_below_93184 blocks_in_93184_95232

end SptClassification.Sieve
