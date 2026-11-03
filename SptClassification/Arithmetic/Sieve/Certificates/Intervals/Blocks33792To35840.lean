/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 33792 through 35839 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_33792_33855 :
    ∀ i : Fin 64, indexedBlockCheck (33792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33856_33919 :
    ∀ i : Fin 64, indexedBlockCheck (33856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33920_33983 :
    ∀ i : Fin 64, indexedBlockCheck (33920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33984_34047 :
    ∀ i : Fin 64, indexedBlockCheck (33984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34048_34111 :
    ∀ i : Fin 64, indexedBlockCheck (34048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34112_34175 :
    ∀ i : Fin 64, indexedBlockCheck (34112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34176_34239 :
    ∀ i : Fin 64, indexedBlockCheck (34176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34240_34303 :
    ∀ i : Fin 64, indexedBlockCheck (34240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33792_34303 :
    ∀ i : Fin 512, indexedBlockCheck (33792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33792 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 33792 0 64 h0 checkBlocks_33792_33855
  have h128 := extendCertifiedSegment 33792 64 64 h64 checkBlocks_33856_33919
  have h192 := extendCertifiedSegment 33792 128 64 h128 checkBlocks_33920_33983
  have h256 := extendCertifiedSegment 33792 192 64 h192 checkBlocks_33984_34047
  have h320 := extendCertifiedSegment 33792 256 64 h256 checkBlocks_34048_34111
  have h384 := extendCertifiedSegment 33792 320 64 h320 checkBlocks_34112_34175
  have h448 := extendCertifiedSegment 33792 384 64 h384 checkBlocks_34176_34239
  have h512 := extendCertifiedSegment 33792 448 64 h448 checkBlocks_34240_34303
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_34304_34367 :
    ∀ i : Fin 64, indexedBlockCheck (34304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34368_34431 :
    ∀ i : Fin 64, indexedBlockCheck (34368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34432_34495 :
    ∀ i : Fin 64, indexedBlockCheck (34432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34496_34559 :
    ∀ i : Fin 64, indexedBlockCheck (34496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34560_34623 :
    ∀ i : Fin 64, indexedBlockCheck (34560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34624_34687 :
    ∀ i : Fin 64, indexedBlockCheck (34624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34688_34751 :
    ∀ i : Fin 64, indexedBlockCheck (34688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34752_34815 :
    ∀ i : Fin 64, indexedBlockCheck (34752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34304_34815 :
    ∀ i : Fin 512, indexedBlockCheck (34304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34304 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 34304 0 64 h0 checkBlocks_34304_34367
  have h128 := extendCertifiedSegment 34304 64 64 h64 checkBlocks_34368_34431
  have h192 := extendCertifiedSegment 34304 128 64 h128 checkBlocks_34432_34495
  have h256 := extendCertifiedSegment 34304 192 64 h192 checkBlocks_34496_34559
  have h320 := extendCertifiedSegment 34304 256 64 h256 checkBlocks_34560_34623
  have h384 := extendCertifiedSegment 34304 320 64 h320 checkBlocks_34624_34687
  have h448 := extendCertifiedSegment 34304 384 64 h384 checkBlocks_34688_34751
  have h512 := extendCertifiedSegment 34304 448 64 h448 checkBlocks_34752_34815
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_34816_34879 :
    ∀ i : Fin 64, indexedBlockCheck (34816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34880_34943 :
    ∀ i : Fin 64, indexedBlockCheck (34880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34944_35007 :
    ∀ i : Fin 64, indexedBlockCheck (34944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35008_35071 :
    ∀ i : Fin 64, indexedBlockCheck (35008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35072_35135 :
    ∀ i : Fin 64, indexedBlockCheck (35072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35136_35199 :
    ∀ i : Fin 64, indexedBlockCheck (35136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35200_35263 :
    ∀ i : Fin 64, indexedBlockCheck (35200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35264_35327 :
    ∀ i : Fin 64, indexedBlockCheck (35264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34816_35327 :
    ∀ i : Fin 512, indexedBlockCheck (34816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34816 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 34816 0 64 h0 checkBlocks_34816_34879
  have h128 := extendCertifiedSegment 34816 64 64 h64 checkBlocks_34880_34943
  have h192 := extendCertifiedSegment 34816 128 64 h128 checkBlocks_34944_35007
  have h256 := extendCertifiedSegment 34816 192 64 h192 checkBlocks_35008_35071
  have h320 := extendCertifiedSegment 34816 256 64 h256 checkBlocks_35072_35135
  have h384 := extendCertifiedSegment 34816 320 64 h320 checkBlocks_35136_35199
  have h448 := extendCertifiedSegment 34816 384 64 h384 checkBlocks_35200_35263
  have h512 := extendCertifiedSegment 34816 448 64 h448 checkBlocks_35264_35327
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_35328_35391 :
    ∀ i : Fin 64, indexedBlockCheck (35328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35392_35455 :
    ∀ i : Fin 64, indexedBlockCheck (35392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35456_35519 :
    ∀ i : Fin 64, indexedBlockCheck (35456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35520_35583 :
    ∀ i : Fin 64, indexedBlockCheck (35520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35584_35647 :
    ∀ i : Fin 64, indexedBlockCheck (35584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35648_35711 :
    ∀ i : Fin 64, indexedBlockCheck (35648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35712_35775 :
    ∀ i : Fin 64, indexedBlockCheck (35712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35776_35839 :
    ∀ i : Fin 64, indexedBlockCheck (35776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35328_35839 :
    ∀ i : Fin 512, indexedBlockCheck (35328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35328 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 35328 0 64 h0 checkBlocks_35328_35391
  have h128 := extendCertifiedSegment 35328 64 64 h64 checkBlocks_35392_35455
  have h192 := extendCertifiedSegment 35328 128 64 h128 checkBlocks_35456_35519
  have h256 := extendCertifiedSegment 35328 192 64 h192 checkBlocks_35520_35583
  have h320 := extendCertifiedSegment 35328 256 64 h256 checkBlocks_35584_35647
  have h384 := extendCertifiedSegment 35328 320 64 h320 checkBlocks_35648_35711
  have h448 := extendCertifiedSegment 35328 384 64 h384 checkBlocks_35712_35775
  have h512 := extendCertifiedSegment 35328 448 64 h448 checkBlocks_35776_35839
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [33792, 35840) passes the packed checker. -/
public theorem blocks_in_33792_35840 :
    ∀ i : Fin 2048, indexedBlockCheck (33792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33792 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 33792 0 512 h0 checkBlocks_33792_34303
  have h1024 := extendCertifiedSegment 33792 512 512 h512 checkBlocks_34304_34815
  have h1536 := extendCertifiedSegment 33792 1024 512 h1024 checkBlocks_34816_35327
  have h2048 := extendCertifiedSegment 33792 1536 512 h1536 checkBlocks_35328_35839
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
