/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 58368 through 60415 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_58368_58431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58368_58431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58368_58431 :
    ∀ i : Fin 64, indexedBlockCheck (58368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58368 0 32 h0 checkBlocks_58368_58431_part0
  have h64 := extendCertifiedSegment 58368 32 32 h32 checkBlocks_58368_58431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58432_58495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58432_58495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58432_58495 :
    ∀ i : Fin 64, indexedBlockCheck (58432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58432 0 32 h0 checkBlocks_58432_58495_part0
  have h64 := extendCertifiedSegment 58432 32 32 h32 checkBlocks_58432_58495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58496_58559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58496_58559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58496_58559 :
    ∀ i : Fin 64, indexedBlockCheck (58496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58496 0 32 h0 checkBlocks_58496_58559_part0
  have h64 := extendCertifiedSegment 58496 32 32 h32 checkBlocks_58496_58559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58560_58623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58560_58623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58560_58623 :
    ∀ i : Fin 64, indexedBlockCheck (58560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58560 0 32 h0 checkBlocks_58560_58623_part0
  have h64 := extendCertifiedSegment 58560 32 32 h32 checkBlocks_58560_58623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58624_58687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58624_58687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58624_58687 :
    ∀ i : Fin 64, indexedBlockCheck (58624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58624 0 32 h0 checkBlocks_58624_58687_part0
  have h64 := extendCertifiedSegment 58624 32 32 h32 checkBlocks_58624_58687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58688_58751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58688_58751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58688_58751 :
    ∀ i : Fin 64, indexedBlockCheck (58688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58688 0 32 h0 checkBlocks_58688_58751_part0
  have h64 := extendCertifiedSegment 58688 32 32 h32 checkBlocks_58688_58751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58752_58815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58752_58815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58752_58815 :
    ∀ i : Fin 64, indexedBlockCheck (58752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58752 0 32 h0 checkBlocks_58752_58815_part0
  have h64 := extendCertifiedSegment 58752 32 32 h32 checkBlocks_58752_58815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58816_58879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58816_58879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58816_58879 :
    ∀ i : Fin 64, indexedBlockCheck (58816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58816 0 32 h0 checkBlocks_58816_58879_part0
  have h64 := extendCertifiedSegment 58816 32 32 h32 checkBlocks_58816_58879_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_58880_58943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58880_58943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58880_58943 :
    ∀ i : Fin 64, indexedBlockCheck (58880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58880 0 32 h0 checkBlocks_58880_58943_part0
  have h64 := extendCertifiedSegment 58880 32 32 h32 checkBlocks_58880_58943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_58944_59007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (58944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58944_59007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (58976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_58944_59007 :
    ∀ i : Fin 64, indexedBlockCheck (58944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (58944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 58944 0 32 h0 checkBlocks_58944_59007_part0
  have h64 := extendCertifiedSegment 58944 32 32 h32 checkBlocks_58944_59007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59008_59071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59008_59071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59008_59071 :
    ∀ i : Fin 64, indexedBlockCheck (59008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59008 0 32 h0 checkBlocks_59008_59071_part0
  have h64 := extendCertifiedSegment 59008 32 32 h32 checkBlocks_59008_59071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59072_59135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59072_59135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59072_59135 :
    ∀ i : Fin 64, indexedBlockCheck (59072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59072 0 32 h0 checkBlocks_59072_59135_part0
  have h64 := extendCertifiedSegment 59072 32 32 h32 checkBlocks_59072_59135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59136_59199_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59136_59199_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59136_59199 :
    ∀ i : Fin 64, indexedBlockCheck (59136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59136 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59136 0 32 h0 checkBlocks_59136_59199_part0
  have h64 := extendCertifiedSegment 59136 32 32 h32 checkBlocks_59136_59199_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59200_59263_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59200_59263_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59200_59263 :
    ∀ i : Fin 64, indexedBlockCheck (59200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59200 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59200 0 32 h0 checkBlocks_59200_59263_part0
  have h64 := extendCertifiedSegment 59200 32 32 h32 checkBlocks_59200_59263_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59264_59327_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59264_59327_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59264_59327 :
    ∀ i : Fin 64, indexedBlockCheck (59264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59264 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59264 0 32 h0 checkBlocks_59264_59327_part0
  have h64 := extendCertifiedSegment 59264 32 32 h32 checkBlocks_59264_59327_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59328_59391_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59328_59391_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59328_59391 :
    ∀ i : Fin 64, indexedBlockCheck (59328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59328 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59328 0 32 h0 checkBlocks_59328_59391_part0
  have h64 := extendCertifiedSegment 59328 32 32 h32 checkBlocks_59328_59391_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_59392_59455_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59392_59455_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59392_59455 :
    ∀ i : Fin 64, indexedBlockCheck (59392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59392 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59392 0 32 h0 checkBlocks_59392_59455_part0
  have h64 := extendCertifiedSegment 59392 32 32 h32 checkBlocks_59392_59455_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59456_59519_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59456_59519_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59456_59519 :
    ∀ i : Fin 64, indexedBlockCheck (59456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59456 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59456 0 32 h0 checkBlocks_59456_59519_part0
  have h64 := extendCertifiedSegment 59456 32 32 h32 checkBlocks_59456_59519_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59520_59583_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59520_59583_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59520_59583 :
    ∀ i : Fin 64, indexedBlockCheck (59520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59520 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59520 0 32 h0 checkBlocks_59520_59583_part0
  have h64 := extendCertifiedSegment 59520 32 32 h32 checkBlocks_59520_59583_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59584_59647_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59584_59647_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59584_59647 :
    ∀ i : Fin 64, indexedBlockCheck (59584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59584 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59584 0 32 h0 checkBlocks_59584_59647_part0
  have h64 := extendCertifiedSegment 59584 32 32 h32 checkBlocks_59584_59647_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59648_59711_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59648_59711_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59648_59711 :
    ∀ i : Fin 64, indexedBlockCheck (59648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59648 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59648 0 32 h0 checkBlocks_59648_59711_part0
  have h64 := extendCertifiedSegment 59648 32 32 h32 checkBlocks_59648_59711_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59712_59775_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59712_59775_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59712_59775 :
    ∀ i : Fin 64, indexedBlockCheck (59712 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59712 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59712 0 32 h0 checkBlocks_59712_59775_part0
  have h64 := extendCertifiedSegment 59712 32 32 h32 checkBlocks_59712_59775_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59776_59839_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59776_59839_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59776_59839 :
    ∀ i : Fin 64, indexedBlockCheck (59776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59776 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59776 0 32 h0 checkBlocks_59776_59839_part0
  have h64 := extendCertifiedSegment 59776 32 32 h32 checkBlocks_59776_59839_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59840_59903_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59840_59903_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59840_59903 :
    ∀ i : Fin 64, indexedBlockCheck (59840 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59840 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59840 0 32 h0 checkBlocks_59840_59903_part0
  have h64 := extendCertifiedSegment 59840 32 32 h32 checkBlocks_59840_59903_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_59904_59967_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59904_59967_part1 :
    ∀ i : Fin 32, indexedBlockCheck (59936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59904_59967 :
    ∀ i : Fin 64, indexedBlockCheck (59904 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59904 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59904 0 32 h0 checkBlocks_59904_59967_part0
  have h64 := extendCertifiedSegment 59904 32 32 h32 checkBlocks_59904_59967_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_59968_60031_part0 :
    ∀ i : Fin 32, indexedBlockCheck (59968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59968_60031_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_59968_60031 :
    ∀ i : Fin 64, indexedBlockCheck (59968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (59968 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 59968 0 32 h0 checkBlocks_59968_60031_part0
  have h64 := extendCertifiedSegment 59968 32 32 h32 checkBlocks_59968_60031_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60032_60095_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60032_60095_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60032_60095 :
    ∀ i : Fin 64, indexedBlockCheck (60032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60032 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60032 0 32 h0 checkBlocks_60032_60095_part0
  have h64 := extendCertifiedSegment 60032 32 32 h32 checkBlocks_60032_60095_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60096_60159_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60096_60159_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60096_60159 :
    ∀ i : Fin 64, indexedBlockCheck (60096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60096 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60096 0 32 h0 checkBlocks_60096_60159_part0
  have h64 := extendCertifiedSegment 60096 32 32 h32 checkBlocks_60096_60159_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60160_60223_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60160_60223_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60160_60223 :
    ∀ i : Fin 64, indexedBlockCheck (60160 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60160 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60160 0 32 h0 checkBlocks_60160_60223_part0
  have h64 := extendCertifiedSegment 60160 32 32 h32 checkBlocks_60160_60223_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60224_60287_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60224_60287_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60224_60287 :
    ∀ i : Fin 64, indexedBlockCheck (60224 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60224 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60224 0 32 h0 checkBlocks_60224_60287_part0
  have h64 := extendCertifiedSegment 60224 32 32 h32 checkBlocks_60224_60287_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60288_60351_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60288_60351_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60288_60351 :
    ∀ i : Fin 64, indexedBlockCheck (60288 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60288 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60288 0 32 h0 checkBlocks_60288_60351_part0
  have h64 := extendCertifiedSegment 60288 32 32 h32 checkBlocks_60288_60351_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60352_60415_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60352_60415_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60352_60415 :
    ∀ i : Fin 64, indexedBlockCheck (60352 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60352 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60352 0 32 h0 checkBlocks_60352_60415_part0
  have h64 := extendCertifiedSegment 60352 32 32 h32 checkBlocks_60352_60415_part1
  intro i
  exact h64 i.val i.isLt

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
