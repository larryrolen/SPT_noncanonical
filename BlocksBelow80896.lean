/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks78848To80896
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow78848

/-! # Cumulative checker certificate through block 80895 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 80896 passes the packed checker. -/
public theorem blocks_below_80896 : ∀ k : ℕ, k < 80896 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 78848 2048 blocks_below_78848 blocks_in_78848_80896

end SptClassification.Sieve
