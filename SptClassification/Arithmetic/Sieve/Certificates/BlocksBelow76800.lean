/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks74752To76800
public import SptClassification.Arithmetic.Sieve.Certificates.BlocksBelow74752

/-! # Cumulative checker certificate through block 76799 -/

public section

namespace SptClassification.Sieve

/-- Every source-range block with index below 76800 passes the packed checker. -/
public theorem blocks_below_76800 : ∀ k : ℕ, k < 76800 → indexedBlockCheck k = true := by
  exact extendCertifiedPrefix 74752 2048 blocks_below_74752 blocks_in_74752_76800

end SptClassification.Sieve
