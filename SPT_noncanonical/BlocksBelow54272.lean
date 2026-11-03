/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks52224To54272
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow52224

/-! # Cumulative checker certificate through block 54271 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 54272 passes the packed checker. -/
public theorem blocks_below_54272 : ∀ k : ℕ, k < 54272 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 52224 2048 blocks_below_52224 blocks_in_52224_54272

end SptClassification.Sieve
