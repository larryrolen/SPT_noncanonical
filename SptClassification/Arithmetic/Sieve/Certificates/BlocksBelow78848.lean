/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks76800To78848
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow76800

/-! # Cumulative checker certificate through block 78847 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 78848 passes the packed checker. -/
public theorem blocks_below_78848 : ∀ k : ℕ, k < 78848 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 76800 2048 blocks_below_76800 blocks_in_76800_78848

end SptClassification.Sieve
