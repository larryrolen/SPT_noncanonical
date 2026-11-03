/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks41984To44032
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow41984

/-! # Cumulative checker certificate through block 44031 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 44032 passes the packed checker. -/
public theorem blocks_below_44032 : ∀ k : ℕ, k < 44032 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 41984 2048 blocks_below_41984 blocks_in_41984_44032

end SptClassification.Sieve
