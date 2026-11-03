/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 17408 through 19455 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_17408_17471 :
    ∀ i : Fin 64, indexedBlockCheck (17408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17472_17535 :
    ∀ i : Fin 64, indexedBlockCheck (17472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17536_17599 :
    ∀ i : Fin 64, indexedBlockCheck (17536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17600_17663 :
    ∀ i : Fin 64, indexedBlockCheck (17600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17664_17727 :
    ∀ i : Fin 64, indexedBlockCheck (17664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17728_17791 :
    ∀ i : Fin 64, indexedBlockCheck (17728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17792_17855 :
    ∀ i : Fin 64, indexedBlockCheck (17792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17856_17919 :
    ∀ i : Fin 64, indexedBlockCheck (17856 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_17920_17983 :
    ∀ i : Fin 64, indexedBlockCheck (17920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17984_18047 :
    ∀ i : Fin 64, indexedBlockCheck (17984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18048_18111 :
    ∀ i : Fin 64, indexedBlockCheck (18048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18112_18175 :
    ∀ i : Fin 64, indexedBlockCheck (18112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18176_18239 :
    ∀ i : Fin 64, indexedBlockCheck (18176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18240_18303 :
    ∀ i : Fin 64, indexedBlockCheck (18240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18304_18367 :
    ∀ i : Fin 64, indexedBlockCheck (18304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18368_18431 :
    ∀ i : Fin 64, indexedBlockCheck (18368 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_18432_18495 :
    ∀ i : Fin 64, indexedBlockCheck (18432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18496_18559 :
    ∀ i : Fin 64, indexedBlockCheck (18496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18560_18623 :
    ∀ i : Fin 64, indexedBlockCheck (18560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18624_18687 :
    ∀ i : Fin 64, indexedBlockCheck (18624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18688_18751 :
    ∀ i : Fin 64, indexedBlockCheck (18688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18752_18815 :
    ∀ i : Fin 64, indexedBlockCheck (18752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18816_18879 :
    ∀ i : Fin 64, indexedBlockCheck (18816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_18880_18943 :
    ∀ i : Fin 64, indexedBlockCheck (18880 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_18944_19007 :
    ∀ i : Fin 64, indexedBlockCheck (18944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19008_19071 :
    ∀ i : Fin 64, indexedBlockCheck (19008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19072_19135 :
    ∀ i : Fin 64, indexedBlockCheck (19072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19136_19199 :
    ∀ i : Fin 64, indexedBlockCheck (19136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19200_19263 :
    ∀ i : Fin 64, indexedBlockCheck (19200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19264_19327 :
    ∀ i : Fin 64, indexedBlockCheck (19264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19328_19391 :
    ∀ i : Fin 64, indexedBlockCheck (19328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_19392_19455 :
    ∀ i : Fin 64, indexedBlockCheck (19392 + i.val) = true := by
  decide +kernel

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
