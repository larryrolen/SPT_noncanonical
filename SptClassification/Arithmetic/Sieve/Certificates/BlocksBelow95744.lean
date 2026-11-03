/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks95232To95744
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow95232

/-! # Cumulative checker certificate through block 95743 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 95744 passes the packed checker. -/
public theorem blocks_below_95744 : ∀ k : ℕ, k < 95744 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 95232 512 blocks_below_95232 blocks_in_95232_95744

end SptClassification.Sieve
