/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks0To1024

/-! # Cumulative checker certificate through block 1023 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 1024 passes the packed checker. -/
public theorem blocks_below_1024 : ∀ k : ℕ, k < 1024 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 0 1024 (by intro k hk; omega) blocks_in_0_1024

end SptClassification.Sieve
