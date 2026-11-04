/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 17408 through 19455 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_17408_17471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17408_17471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17408_17471 :
    ∀ i : Fin 64, indexedBlockCheck (17408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17408 0 32 h0 checkBlocks_17408_17471_part0
  have h64 := extendCertifiedSegment 17408 32 32 h32 checkBlocks_17408_17471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17472_17535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17472_17535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17472_17535 :
    ∀ i : Fin 64, indexedBlockCheck (17472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17472 0 32 h0 checkBlocks_17472_17535_part0
  have h64 := extendCertifiedSegment 17472 32 32 h32 checkBlocks_17472_17535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17536_17599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17536_17599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17536_17599 :
    ∀ i : Fin 64, indexedBlockCheck (17536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17536 0 32 h0 checkBlocks_17536_17599_part0
  have h64 := extendCertifiedSegment 17536 32 32 h32 checkBlocks_17536_17599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17600_17663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17600_17663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17600_17663 :
    ∀ i : Fin 64, indexedBlockCheck (17600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17600 0 32 h0 checkBlocks_17600_17663_part0
  have h64 := extendCertifiedSegment 17600 32 32 h32 checkBlocks_17600_17663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17664_17727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17664_17727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17664_17727 :
    ∀ i : Fin 64, indexedBlockCheck (17664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17664 0 32 h0 checkBlocks_17664_17727_part0
  have h64 := extendCertifiedSegment 17664 32 32 h32 checkBlocks_17664_17727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17728_17791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17728_17791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17728_17791 :
    ∀ i : Fin 64, indexedBlockCheck (17728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17728 0 32 h0 checkBlocks_17728_17791_part0
  have h64 := extendCertifiedSegment 17728 32 32 h32 checkBlocks_17728_17791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17792_17855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17792_17855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17792_17855 :
    ∀ i : Fin 64, indexedBlockCheck (17792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17792 0 32 h0 checkBlocks_17792_17855_part0
  have h64 := extendCertifiedSegment 17792 32 32 h32 checkBlocks_17792_17855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17856_17919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17856_17919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17856_17919 :
    ∀ i : Fin 64, indexedBlockCheck (17856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17856 0 32 h0 checkBlocks_17856_17919_part0
  have h64 := extendCertifiedSegment 17856 32 32 h32 checkBlocks_17856_17919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17408_17919 :
    ∀ i : Fin 512, indexedBlockCheck (17408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17408 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 17408 0 64 h0 checkBlocks_17408_17471
  have h128 := extendCertifiedSegment 17408 64 64 h64 checkBlocks_17472_17535
  have h192 := extendCertifiedSegment 17408 128 64 h128 checkBlocks_17536_17599
  have h256 := extendCertifiedSegment 17408 192 64 h192 checkBlocks_17600_17663
  have h320 := extendCertifiedSegment 17408 256 64 h256 checkBlocks_17664_17727
  have h384 := extendCertifiedSegment 17408 320 64 h320 checkBlocks_17728_17791
  have h448 := extendCertifiedSegment 17408 384 64 h384 checkBlocks_17792_17855
  have h512 := extendCertifiedSegment 17408 448 64 h448 checkBlocks_17856_17919
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_17920_17983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17920_17983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17920_17983 :
    ∀ i : Fin 64, indexedBlockCheck (17920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17920 0 32 h0 checkBlocks_17920_17983_part0
  have h64 := extendCertifiedSegment 17920 32 32 h32 checkBlocks_17920_17983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17984_18047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17984_18047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17984_18047 :
    ∀ i : Fin 64, indexedBlockCheck (17984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17984 0 32 h0 checkBlocks_17984_18047_part0
  have h64 := extendCertifiedSegment 17984 32 32 h32 checkBlocks_17984_18047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18048_18111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18048_18111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18048_18111 :
    ∀ i : Fin 64, indexedBlockCheck (18048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18048 0 32 h0 checkBlocks_18048_18111_part0
  have h64 := extendCertifiedSegment 18048 32 32 h32 checkBlocks_18048_18111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18112_18175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18112_18175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18112_18175 :
    ∀ i : Fin 64, indexedBlockCheck (18112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18112 0 32 h0 checkBlocks_18112_18175_part0
  have h64 := extendCertifiedSegment 18112 32 32 h32 checkBlocks_18112_18175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18176_18239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18176_18239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18176_18239 :
    ∀ i : Fin 64, indexedBlockCheck (18176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18176 0 32 h0 checkBlocks_18176_18239_part0
  have h64 := extendCertifiedSegment 18176 32 32 h32 checkBlocks_18176_18239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18240_18303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18240_18303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18240_18303 :
    ∀ i : Fin 64, indexedBlockCheck (18240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18240 0 32 h0 checkBlocks_18240_18303_part0
  have h64 := extendCertifiedSegment 18240 32 32 h32 checkBlocks_18240_18303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18304_18367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18304_18367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18304_18367 :
    ∀ i : Fin 64, indexedBlockCheck (18304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18304 0 32 h0 checkBlocks_18304_18367_part0
  have h64 := extendCertifiedSegment 18304 32 32 h32 checkBlocks_18304_18367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18368_18431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18368_18431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18368_18431 :
    ∀ i : Fin 64, indexedBlockCheck (18368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18368 0 32 h0 checkBlocks_18368_18431_part0
  have h64 := extendCertifiedSegment 18368 32 32 h32 checkBlocks_18368_18431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17920_18431 :
    ∀ i : Fin 512, indexedBlockCheck (17920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17920 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 17920 0 64 h0 checkBlocks_17920_17983
  have h128 := extendCertifiedSegment 17920 64 64 h64 checkBlocks_17984_18047
  have h192 := extendCertifiedSegment 17920 128 64 h128 checkBlocks_18048_18111
  have h256 := extendCertifiedSegment 17920 192 64 h192 checkBlocks_18112_18175
  have h320 := extendCertifiedSegment 17920 256 64 h256 checkBlocks_18176_18239
  have h384 := extendCertifiedSegment 17920 320 64 h320 checkBlocks_18240_18303
  have h448 := extendCertifiedSegment 17920 384 64 h384 checkBlocks_18304_18367
  have h512 := extendCertifiedSegment 17920 448 64 h448 checkBlocks_18368_18431
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_18432_18495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18432_18495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18432_18495 :
    ∀ i : Fin 64, indexedBlockCheck (18432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18432 0 32 h0 checkBlocks_18432_18495_part0
  have h64 := extendCertifiedSegment 18432 32 32 h32 checkBlocks_18432_18495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18496_18559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18496_18559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18496_18559 :
    ∀ i : Fin 64, indexedBlockCheck (18496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18496 0 32 h0 checkBlocks_18496_18559_part0
  have h64 := extendCertifiedSegment 18496 32 32 h32 checkBlocks_18496_18559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18560_18623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18560_18623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18560_18623 :
    ∀ i : Fin 64, indexedBlockCheck (18560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18560 0 32 h0 checkBlocks_18560_18623_part0
  have h64 := extendCertifiedSegment 18560 32 32 h32 checkBlocks_18560_18623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18624_18687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18624_18687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18624_18687 :
    ∀ i : Fin 64, indexedBlockCheck (18624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18624 0 32 h0 checkBlocks_18624_18687_part0
  have h64 := extendCertifiedSegment 18624 32 32 h32 checkBlocks_18624_18687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18688_18751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18688_18751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18688_18751 :
    ∀ i : Fin 64, indexedBlockCheck (18688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18688 0 32 h0 checkBlocks_18688_18751_part0
  have h64 := extendCertifiedSegment 18688 32 32 h32 checkBlocks_18688_18751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18752_18815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18752_18815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18752_18815 :
    ∀ i : Fin 64, indexedBlockCheck (18752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18752 0 32 h0 checkBlocks_18752_18815_part0
  have h64 := extendCertifiedSegment 18752 32 32 h32 checkBlocks_18752_18815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18816_18879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18816_18879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18816_18879 :
    ∀ i : Fin 64, indexedBlockCheck (18816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18816 0 32 h0 checkBlocks_18816_18879_part0
  have h64 := extendCertifiedSegment 18816 32 32 h32 checkBlocks_18816_18879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18880_18943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18880_18943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18880_18943 :
    ∀ i : Fin 64, indexedBlockCheck (18880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18880 0 32 h0 checkBlocks_18880_18943_part0
  have h64 := extendCertifiedSegment 18880 32 32 h32 checkBlocks_18880_18943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18432_18943 :
    ∀ i : Fin 512, indexedBlockCheck (18432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18432 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 18432 0 64 h0 checkBlocks_18432_18495
  have h128 := extendCertifiedSegment 18432 64 64 h64 checkBlocks_18496_18559
  have h192 := extendCertifiedSegment 18432 128 64 h128 checkBlocks_18560_18623
  have h256 := extendCertifiedSegment 18432 192 64 h192 checkBlocks_18624_18687
  have h320 := extendCertifiedSegment 18432 256 64 h256 checkBlocks_18688_18751
  have h384 := extendCertifiedSegment 18432 320 64 h320 checkBlocks_18752_18815
  have h448 := extendCertifiedSegment 18432 384 64 h384 checkBlocks_18816_18879
  have h512 := extendCertifiedSegment 18432 448 64 h448 checkBlocks_18880_18943
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_18944_19007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (18944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18944_19007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (18976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18944_19007 :
    ∀ i : Fin 64, indexedBlockCheck (18944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 18944 0 32 h0 checkBlocks_18944_19007_part0
  have h64 := extendCertifiedSegment 18944 32 32 h32 checkBlocks_18944_19007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19008_19071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19008_19071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19008_19071 :
    ∀ i : Fin 64, indexedBlockCheck (19008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19008 0 32 h0 checkBlocks_19008_19071_part0
  have h64 := extendCertifiedSegment 19008 32 32 h32 checkBlocks_19008_19071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19072_19135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19072_19135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19072_19135 :
    ∀ i : Fin 64, indexedBlockCheck (19072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19072 0 32 h0 checkBlocks_19072_19135_part0
  have h64 := extendCertifiedSegment 19072 32 32 h32 checkBlocks_19072_19135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19136_19199_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19136_19199_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19136_19199 :
    ∀ i : Fin 64, indexedBlockCheck (19136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19136 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19136 0 32 h0 checkBlocks_19136_19199_part0
  have h64 := extendCertifiedSegment 19136 32 32 h32 checkBlocks_19136_19199_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19200_19263_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19200_19263_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19200_19263 :
    ∀ i : Fin 64, indexedBlockCheck (19200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19200 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19200 0 32 h0 checkBlocks_19200_19263_part0
  have h64 := extendCertifiedSegment 19200 32 32 h32 checkBlocks_19200_19263_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19264_19327_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19264_19327_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19264_19327 :
    ∀ i : Fin 64, indexedBlockCheck (19264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19264 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19264 0 32 h0 checkBlocks_19264_19327_part0
  have h64 := extendCertifiedSegment 19264 32 32 h32 checkBlocks_19264_19327_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19328_19391_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19328_19391_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19328_19391 :
    ∀ i : Fin 64, indexedBlockCheck (19328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19328 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19328 0 32 h0 checkBlocks_19328_19391_part0
  have h64 := extendCertifiedSegment 19328 32 32 h32 checkBlocks_19328_19391_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_19392_19455_part0 :
    ∀ i : Fin 32, indexedBlockCheck (19392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19392_19455_part1 :
    ∀ i : Fin 32, indexedBlockCheck (19424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19392_19455 :
    ∀ i : Fin 64, indexedBlockCheck (19392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (19392 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 19392 0 32 h0 checkBlocks_19392_19455_part0
  have h64 := extendCertifiedSegment 19392 32 32 h32 checkBlocks_19392_19455_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_18944_19455 :
    ∀ i : Fin 512, indexedBlockCheck (18944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (18944 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 18944 0 64 h0 checkBlocks_18944_19007
  have h128 := extendCertifiedSegment 18944 64 64 h64 checkBlocks_19008_19071
  have h192 := extendCertifiedSegment 18944 128 64 h128 checkBlocks_19072_19135
  have h256 := extendCertifiedSegment 18944 192 64 h192 checkBlocks_19136_19199
  have h320 := extendCertifiedSegment 18944 256 64 h256 checkBlocks_19200_19263
  have h384 := extendCertifiedSegment 18944 320 64 h320 checkBlocks_19264_19327
  have h448 := extendCertifiedSegment 18944 384 64 h384 checkBlocks_19328_19391
  have h512 := extendCertifiedSegment 18944 448 64 h448 checkBlocks_19392_19455
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [17408, 19456) passes the packed checker. -/
public theorem blocks_in_17408_19456 :
    ∀ i : Fin 2048, indexedBlockCheck (17408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17408 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 17408 0 512 h0 checkBlocks_17408_17919
  have h1024 := extendCertifiedSegment 17408 512 512 h512 checkBlocks_17920_18431
  have h1536 := extendCertifiedSegment 17408 1024 512 h1024 checkBlocks_18432_18943
  have h2048 := extendCertifiedSegment 17408 1536 512 h1536 checkBlocks_18944_19455
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
