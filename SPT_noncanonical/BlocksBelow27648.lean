/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks25600To27648
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow25600

/-! # Cumulative checker certificate through block 27647 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 27648 passes the packed checker. -/
public theorem blocks_below_27648 : ∀ k : ℕ, k < 27648 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 25600 2048 blocks_below_25600 blocks_in_25600_27648

end SptClassification.Sieve
