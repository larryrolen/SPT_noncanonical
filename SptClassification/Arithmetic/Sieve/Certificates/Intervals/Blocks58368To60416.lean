/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 58368 through 60415 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_58368_58431 :
    ∀ i : Fin 64, indexedBlockCheck (58368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58432_58495 :
    ∀ i : Fin 64, indexedBlockCheck (58432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58496_58559 :
    ∀ i : Fin 64, indexedBlockCheck (58496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58560_58623 :
    ∀ i : Fin 64, indexedBlockCheck (58560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58624_58687 :
    ∀ i : Fin 64, indexedBlockCheck (58624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58688_58751 :
    ∀ i : Fin 64, indexedBlockCheck (58688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58752_58815 :
    ∀ i : Fin 64, indexedBlockCheck (58752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58816_58879 :
    ∀ i : Fin 64, indexedBlockCheck (58816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58368_58879 :
    ∀ i : Fin 512, indexedBlockCheck (58368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58368 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 58368 0 64 h0 checkBlocks_58368_58431
  have h128 := extendCertifiedSegment 58368 64 64 h64 checkBlocks_58432_58495
  have h192 := extendCertifiedSegment 58368 128 64 h128 checkBlocks_58496_58559
  have h256 := extendCertifiedSegment 58368 192 64 h192 checkBlocks_58560_58623
  have h320 := extendCertifiedSegment 58368 256 64 h256 checkBlocks_58624_58687
  have h384 := extendCertifiedSegment 58368 320 64 h320 checkBlocks_58688_58751
  have h448 := extendCertifiedSegment 58368 384 64 h384 checkBlocks_58752_58815
  have h512 := extendCertifiedSegment 58368 448 64 h448 checkBlocks_58816_58879
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_58880_58943 :
    ∀ i : Fin 64, indexedBlockCheck (58880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58944_59007 :
    ∀ i : Fin 64, indexedBlockCheck (58944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59008_59071 :
    ∀ i : Fin 64, indexedBlockCheck (59008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59072_59135 :
    ∀ i : Fin 64, indexedBlockCheck (59072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59136_59199 :
    ∀ i : Fin 64, indexedBlockCheck (59136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59200_59263 :
    ∀ i : Fin 64, indexedBlockCheck (59200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59264_59327 :
    ∀ i : Fin 64, indexedBlockCheck (59264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59328_59391 :
    ∀ i : Fin 64, indexedBlockCheck (59328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58880_59391 :
    ∀ i : Fin 512, indexedBlockCheck (58880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58880 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 58880 0 64 h0 checkBlocks_58880_58943
  have h128 := extendCertifiedSegment 58880 64 64 h64 checkBlocks_58944_59007
  have h192 := extendCertifiedSegment 58880 128 64 h128 checkBlocks_59008_59071
  have h256 := extendCertifiedSegment 58880 192 64 h192 checkBlocks_59072_59135
  have h320 := extendCertifiedSegment 58880 256 64 h256 checkBlocks_59136_59199
  have h384 := extendCertifiedSegment 58880 320 64 h320 checkBlocks_59200_59263
  have h448 := extendCertifiedSegment 58880 384 64 h384 checkBlocks_59264_59327
  have h512 := extendCertifiedSegment 58880 448 64 h448 checkBlocks_59328_59391
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_59392_59455 :
    ∀ i : Fin 64, indexedBlockCheck (59392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59456_59519 :
    ∀ i : Fin 64, indexedBlockCheck (59456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59520_59583 :
    ∀ i : Fin 64, indexedBlockCheck (59520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59584_59647 :
    ∀ i : Fin 64, indexedBlockCheck (59584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59648_59711 :
    ∀ i : Fin 64, indexedBlockCheck (59648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59712_59775 :
    ∀ i : Fin 64, indexedBlockCheck (59712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59776_59839 :
    ∀ i : Fin 64, indexedBlockCheck (59776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59840_59903 :
    ∀ i : Fin 64, indexedBlockCheck (59840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59392_59903 :
    ∀ i : Fin 512, indexedBlockCheck (59392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59392 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 59392 0 64 h0 checkBlocks_59392_59455
  have h128 := extendCertifiedSegment 59392 64 64 h64 checkBlocks_59456_59519
  have h192 := extendCertifiedSegment 59392 128 64 h128 checkBlocks_59520_59583
  have h256 := extendCertifiedSegment 59392 192 64 h192 checkBlocks_59584_59647
  have h320 := extendCertifiedSegment 59392 256 64 h256 checkBlocks_59648_59711
  have h384 := extendCertifiedSegment 59392 320 64 h320 checkBlocks_59712_59775
  have h448 := extendCertifiedSegment 59392 384 64 h384 checkBlocks_59776_59839
  have h512 := extendCertifiedSegment 59392 448 64 h448 checkBlocks_59840_59903
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_59904_59967 :
    ∀ i : Fin 64, indexedBlockCheck (59904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59968_60031 :
    ∀ i : Fin 64, indexedBlockCheck (59968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60032_60095 :
    ∀ i : Fin 64, indexedBlockCheck (60032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60096_60159 :
    ∀ i : Fin 64, indexedBlockCheck (60096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60160_60223 :
    ∀ i : Fin 64, indexedBlockCheck (60160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60224_60287 :
    ∀ i : Fin 64, indexedBlockCheck (60224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60288_60351 :
    ∀ i : Fin 64, indexedBlockCheck (60288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60352_60415 :
    ∀ i : Fin 64, indexedBlockCheck (60352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59904_60415 :
    ∀ i : Fin 512, indexedBlockCheck (59904 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59904 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 59904 0 64 h0 checkBlocks_59904_59967
  have h128 := extendCertifiedSegment 59904 64 64 h64 checkBlocks_59968_60031
  have h192 := extendCertifiedSegment 59904 128 64 h128 checkBlocks_60032_60095
  have h256 := extendCertifiedSegment 59904 192 64 h192 checkBlocks_60096_60159
  have h320 := extendCertifiedSegment 59904 256 64 h256 checkBlocks_60160_60223
  have h384 := extendCertifiedSegment 59904 320 64 h320 checkBlocks_60224_60287
  have h448 := extendCertifiedSegment 59904 384 64 h384 checkBlocks_60288_60351
  have h512 := extendCertifiedSegment 59904 448 64 h448 checkBlocks_60352_60415
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [58368, 60416) passes the packed checker. -/
public theorem blocks_in_58368_60416 :
    ∀ i : Fin 2048, indexedBlockCheck (58368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58368 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 58368 0 512 h0 checkBlocks_58368_58879
  have h1024 := extendCertifiedSegment 58368 512 512 h512 checkBlocks_58880_59391
  have h1536 := extendCertifiedSegment 58368 1024 512 h1024 checkBlocks_59392_59903
  have h2048 := extendCertifiedSegment 58368 1536 512 h1536 checkBlocks_59904_60415
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
