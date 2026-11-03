/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks87040To89088
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow87040

/-! # Cumulative checker certificate through block 89087 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 89088 passes the packed checker. -/
public theorem blocks_below_89088 : ∀ k : ℕ, k < 89088 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 87040 2048 blocks_below_87040 blocks_in_87040_89088

end SptClassification.Sieve
