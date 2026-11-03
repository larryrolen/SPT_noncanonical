/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks50176To52224
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow50176

/-! # Cumulative checker certificate through block 52223 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 52224 passes the packed checker. -/
public theorem blocks_below_52224 : ∀ k : ℕ, k < 52224 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 50176 2048 blocks_below_50176 blocks_in_50176_52224

end SptClassification.Sieve
