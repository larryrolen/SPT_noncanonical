/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 11264 through 13311 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_11264_11327_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11264_11327_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11264_11327 :
    ∀ i : Fin 64, indexedBlockCheck (11264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11264 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11264 0 32 h0 checkBlocks_11264_11327_part0
  have h64 := extendCertifiedSegment 11264 32 32 h32 checkBlocks_11264_11327_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11328_11391_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11328_11391_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11328_11391 :
    ∀ i : Fin 64, indexedBlockCheck (11328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11328 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11328 0 32 h0 checkBlocks_11328_11391_part0
  have h64 := extendCertifiedSegment 11328 32 32 h32 checkBlocks_11328_11391_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11392_11455_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11392_11455_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11392_11455 :
    ∀ i : Fin 64, indexedBlockCheck (11392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11392 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11392 0 32 h0 checkBlocks_11392_11455_part0
  have h64 := extendCertifiedSegment 11392 32 32 h32 checkBlocks_11392_11455_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11456_11519_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11456_11519_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11456_11519 :
    ∀ i : Fin 64, indexedBlockCheck (11456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11456 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11456 0 32 h0 checkBlocks_11456_11519_part0
  have h64 := extendCertifiedSegment 11456 32 32 h32 checkBlocks_11456_11519_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11520_11583_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11520_11583_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11520_11583 :
    ∀ i : Fin 64, indexedBlockCheck (11520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11520 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11520 0 32 h0 checkBlocks_11520_11583_part0
  have h64 := extendCertifiedSegment 11520 32 32 h32 checkBlocks_11520_11583_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11584_11647_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11584_11647_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11584_11647 :
    ∀ i : Fin 64, indexedBlockCheck (11584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11584 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11584 0 32 h0 checkBlocks_11584_11647_part0
  have h64 := extendCertifiedSegment 11584 32 32 h32 checkBlocks_11584_11647_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11648_11711_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11648_11711_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11648_11711 :
    ∀ i : Fin 64, indexedBlockCheck (11648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11648 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11648 0 32 h0 checkBlocks_11648_11711_part0
  have h64 := extendCertifiedSegment 11648 32 32 h32 checkBlocks_11648_11711_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11712_11775_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11712_11775_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11712_11775 :
    ∀ i : Fin 64, indexedBlockCheck (11712 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11712 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11712 0 32 h0 checkBlocks_11712_11775_part0
  have h64 := extendCertifiedSegment 11712 32 32 h32 checkBlocks_11712_11775_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11264_11775 :
    ∀ i : Fin 512, indexedBlockCheck (11264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11264 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 11264 0 64 h0 checkBlocks_11264_11327
  have h128 := extendCertifiedSegment 11264 64 64 h64 checkBlocks_11328_11391
  have h192 := extendCertifiedSegment 11264 128 64 h128 checkBlocks_11392_11455
  have h256 := extendCertifiedSegment 11264 192 64 h192 checkBlocks_11456_11519
  have h320 := extendCertifiedSegment 11264 256 64 h256 checkBlocks_11520_11583
  have h384 := extendCertifiedSegment 11264 320 64 h320 checkBlocks_11584_11647
  have h448 := extendCertifiedSegment 11264 384 64 h384 checkBlocks_11648_11711
  have h512 := extendCertifiedSegment 11264 448 64 h448 checkBlocks_11712_11775
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_11776_11839_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11776_11839_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11776_11839 :
    ∀ i : Fin 64, indexedBlockCheck (11776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11776 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11776 0 32 h0 checkBlocks_11776_11839_part0
  have h64 := extendCertifiedSegment 11776 32 32 h32 checkBlocks_11776_11839_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11840_11903_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11840_11903_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11840_11903 :
    ∀ i : Fin 64, indexedBlockCheck (11840 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11840 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11840 0 32 h0 checkBlocks_11840_11903_part0
  have h64 := extendCertifiedSegment 11840 32 32 h32 checkBlocks_11840_11903_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11904_11967_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11904_11967_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11904_11967 :
    ∀ i : Fin 64, indexedBlockCheck (11904 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11904 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11904 0 32 h0 checkBlocks_11904_11967_part0
  have h64 := extendCertifiedSegment 11904 32 32 h32 checkBlocks_11904_11967_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11968_12031_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11968_12031_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11968_12031 :
    ∀ i : Fin 64, indexedBlockCheck (11968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11968 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11968 0 32 h0 checkBlocks_11968_12031_part0
  have h64 := extendCertifiedSegment 11968 32 32 h32 checkBlocks_11968_12031_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12032_12095_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12032_12095_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12032_12095 :
    ∀ i : Fin 64, indexedBlockCheck (12032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12032 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12032 0 32 h0 checkBlocks_12032_12095_part0
  have h64 := extendCertifiedSegment 12032 32 32 h32 checkBlocks_12032_12095_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12096_12159_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12096_12159_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12096_12159 :
    ∀ i : Fin 64, indexedBlockCheck (12096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12096 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12096 0 32 h0 checkBlocks_12096_12159_part0
  have h64 := extendCertifiedSegment 12096 32 32 h32 checkBlocks_12096_12159_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12160_12223_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12160_12223_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12160_12223 :
    ∀ i : Fin 64, indexedBlockCheck (12160 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12160 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12160 0 32 h0 checkBlocks_12160_12223_part0
  have h64 := extendCertifiedSegment 12160 32 32 h32 checkBlocks_12160_12223_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12224_12287_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12224_12287_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12224_12287 :
    ∀ i : Fin 64, indexedBlockCheck (12224 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12224 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12224 0 32 h0 checkBlocks_12224_12287_part0
  have h64 := extendCertifiedSegment 12224 32 32 h32 checkBlocks_12224_12287_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11776_12287 :
    ∀ i : Fin 512, indexedBlockCheck (11776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11776 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 11776 0 64 h0 checkBlocks_11776_11839
  have h128 := extendCertifiedSegment 11776 64 64 h64 checkBlocks_11840_11903
  have h192 := extendCertifiedSegment 11776 128 64 h128 checkBlocks_11904_11967
  have h256 := extendCertifiedSegment 11776 192 64 h192 checkBlocks_11968_12031
  have h320 := extendCertifiedSegment 11776 256 64 h256 checkBlocks_12032_12095
  have h384 := extendCertifiedSegment 11776 320 64 h320 checkBlocks_12096_12159
  have h448 := extendCertifiedSegment 11776 384 64 h384 checkBlocks_12160_12223
  have h512 := extendCertifiedSegment 11776 448 64 h448 checkBlocks_12224_12287
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_12288_12351_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12288_12351_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12288_12351 :
    ∀ i : Fin 64, indexedBlockCheck (12288 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12288 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12288 0 32 h0 checkBlocks_12288_12351_part0
  have h64 := extendCertifiedSegment 12288 32 32 h32 checkBlocks_12288_12351_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12352_12415_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12352_12415_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12352_12415 :
    ∀ i : Fin 64, indexedBlockCheck (12352 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12352 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12352 0 32 h0 checkBlocks_12352_12415_part0
  have h64 := extendCertifiedSegment 12352 32 32 h32 checkBlocks_12352_12415_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12416_12479_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12416_12479_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12416_12479 :
    ∀ i : Fin 64, indexedBlockCheck (12416 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12416 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12416 0 32 h0 checkBlocks_12416_12479_part0
  have h64 := extendCertifiedSegment 12416 32 32 h32 checkBlocks_12416_12479_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12480_12543_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12480_12543_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12480_12543 :
    ∀ i : Fin 64, indexedBlockCheck (12480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12480 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12480 0 32 h0 checkBlocks_12480_12543_part0
  have h64 := extendCertifiedSegment 12480 32 32 h32 checkBlocks_12480_12543_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12544_12607_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12544_12607_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12544_12607 :
    ∀ i : Fin 64, indexedBlockCheck (12544 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12544 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12544 0 32 h0 checkBlocks_12544_12607_part0
  have h64 := extendCertifiedSegment 12544 32 32 h32 checkBlocks_12544_12607_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12608_12671_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12608_12671_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12608_12671 :
    ∀ i : Fin 64, indexedBlockCheck (12608 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12608 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12608 0 32 h0 checkBlocks_12608_12671_part0
  have h64 := extendCertifiedSegment 12608 32 32 h32 checkBlocks_12608_12671_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12672_12735_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12672_12735_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12672_12735 :
    ∀ i : Fin 64, indexedBlockCheck (12672 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12672 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12672 0 32 h0 checkBlocks_12672_12735_part0
  have h64 := extendCertifiedSegment 12672 32 32 h32 checkBlocks_12672_12735_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12736_12799_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12736_12799_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12736_12799 :
    ∀ i : Fin 64, indexedBlockCheck (12736 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12736 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12736 0 32 h0 checkBlocks_12736_12799_part0
  have h64 := extendCertifiedSegment 12736 32 32 h32 checkBlocks_12736_12799_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12288_12799 :
    ∀ i : Fin 512, indexedBlockCheck (12288 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12288 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 12288 0 64 h0 checkBlocks_12288_12351
  have h128 := extendCertifiedSegment 12288 64 64 h64 checkBlocks_12352_12415
  have h192 := extendCertifiedSegment 12288 128 64 h128 checkBlocks_12416_12479
  have h256 := extendCertifiedSegment 12288 192 64 h192 checkBlocks_12480_12543
  have h320 := extendCertifiedSegment 12288 256 64 h256 checkBlocks_12544_12607
  have h384 := extendCertifiedSegment 12288 320 64 h320 checkBlocks_12608_12671
  have h448 := extendCertifiedSegment 12288 384 64 h384 checkBlocks_12672_12735
  have h512 := extendCertifiedSegment 12288 448 64 h448 checkBlocks_12736_12799
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_12800_12863_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12800_12863_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12800_12863 :
    ∀ i : Fin 64, indexedBlockCheck (12800 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12800 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12800 0 32 h0 checkBlocks_12800_12863_part0
  have h64 := extendCertifiedSegment 12800 32 32 h32 checkBlocks_12800_12863_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12864_12927_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12864_12927_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12864_12927 :
    ∀ i : Fin 64, indexedBlockCheck (12864 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12864 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12864 0 32 h0 checkBlocks_12864_12927_part0
  have h64 := extendCertifiedSegment 12864 32 32 h32 checkBlocks_12864_12927_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12928_12991_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12928_12991_part1 :
    ∀ i : Fin 32, indexedBlockCheck (12960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12928_12991 :
    ∀ i : Fin 64, indexedBlockCheck (12928 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12928 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12928 0 32 h0 checkBlocks_12928_12991_part0
  have h64 := extendCertifiedSegment 12928 32 32 h32 checkBlocks_12928_12991_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12992_13055_part0 :
    ∀ i : Fin 32, indexedBlockCheck (12992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12992_13055_part1 :
    ∀ i : Fin 32, indexedBlockCheck (13024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_12992_13055 :
    ∀ i : Fin 64, indexedBlockCheck (12992 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12992 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 12992 0 32 h0 checkBlocks_12992_13055_part0
  have h64 := extendCertifiedSegment 12992 32 32 h32 checkBlocks_12992_13055_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_13056_13119_part0 :
    ∀ i : Fin 32, indexedBlockCheck (13056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13056_13119_part1 :
    ∀ i : Fin 32, indexedBlockCheck (13088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13056_13119 :
    ∀ i : Fin 64, indexedBlockCheck (13056 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (13056 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 13056 0 32 h0 checkBlocks_13056_13119_part0
  have h64 := extendCertifiedSegment 13056 32 32 h32 checkBlocks_13056_13119_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_13120_13183_part0 :
    ∀ i : Fin 32, indexedBlockCheck (13120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13120_13183_part1 :
    ∀ i : Fin 32, indexedBlockCheck (13152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13120_13183 :
    ∀ i : Fin 64, indexedBlockCheck (13120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (13120 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 13120 0 32 h0 checkBlocks_13120_13183_part0
  have h64 := extendCertifiedSegment 13120 32 32 h32 checkBlocks_13120_13183_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_13184_13247_part0 :
    ∀ i : Fin 32, indexedBlockCheck (13184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13184_13247_part1 :
    ∀ i : Fin 32, indexedBlockCheck (13216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13184_13247 :
    ∀ i : Fin 64, indexedBlockCheck (13184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (13184 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 13184 0 32 h0 checkBlocks_13184_13247_part0
  have h64 := extendCertifiedSegment 13184 32 32 h32 checkBlocks_13184_13247_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_13248_13311_part0 :
    ∀ i : Fin 32, indexedBlockCheck (13248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13248_13311_part1 :
    ∀ i : Fin 32, indexedBlockCheck (13280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13248_13311 :
    ∀ i : Fin 64, indexedBlockCheck (13248 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (13248 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 13248 0 32 h0 checkBlocks_13248_13311_part0
  have h64 := extendCertifiedSegment 13248 32 32 h32 checkBlocks_13248_13311_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_12800_13311 :
    ∀ i : Fin 512, indexedBlockCheck (12800 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (12800 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 12800 0 64 h0 checkBlocks_12800_12863
  have h128 := extendCertifiedSegment 12800 64 64 h64 checkBlocks_12864_12927
  have h192 := extendCertifiedSegment 12800 128 64 h128 checkBlocks_12928_12991
  have h256 := extendCertifiedSegment 12800 192 64 h192 checkBlocks_12992_13055
  have h320 := extendCertifiedSegment 12800 256 64 h256 checkBlocks_13056_13119
  have h384 := extendCertifiedSegment 12800 320 64 h320 checkBlocks_13120_13183
  have h448 := extendCertifiedSegment 12800 384 64 h384 checkBlocks_13184_13247
  have h512 := extendCertifiedSegment 12800 448 64 h448 checkBlocks_13248_13311
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [11264, 13312) passes the packed checker. -/
public theorem blocks_in_11264_13312 :
    ∀ i : Fin 2048, indexedBlockCheck (11264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11264 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 11264 0 512 h0 checkBlocks_11264_11775
  have h1024 := extendCertifiedSegment 11264 512 512 h512 checkBlocks_11776_12287
  have h1536 := extendCertifiedSegment 11264 1024 512 h1024 checkBlocks_12288_12799
  have h2048 := extendCertifiedSegment 11264 1536 512 h1536 checkBlocks_12800_13311
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
