/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks84992To87040
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow84992

/-! # Cumulative checker certificate through block 87039 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 87040 passes the packed checker. -/
public theorem blocks_below_87040 : ∀ k : ℕ, k < 87040 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 84992 2048 blocks_below_84992 blocks_in_84992_87040

end SptClassification.Sieve
