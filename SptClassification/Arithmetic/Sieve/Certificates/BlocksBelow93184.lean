/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks91136To93184
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow91136

/-! # Cumulative checker certificate through block 93183 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 93184 passes the packed checker. -/
public theorem blocks_below_93184 : ∀ k : ℕ, k < 93184 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 91136 2048 blocks_below_91136 blocks_in_91136_93184

end SptClassification.Sieve
