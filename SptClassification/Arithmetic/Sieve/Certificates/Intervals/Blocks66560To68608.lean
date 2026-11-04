/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 66560 through 68607 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_66560_66623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66560_66623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66560_66623 :
    ∀ i : Fin 64, indexedBlockCheck (66560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66560 0 32 h0 checkBlocks_66560_66623_part0
  have h64 := extendCertifiedSegment 66560 32 32 h32 checkBlocks_66560_66623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66624_66687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66624_66687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66624_66687 :
    ∀ i : Fin 64, indexedBlockCheck (66624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66624 0 32 h0 checkBlocks_66624_66687_part0
  have h64 := extendCertifiedSegment 66624 32 32 h32 checkBlocks_66624_66687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66688_66751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66688_66751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66688_66751 :
    ∀ i : Fin 64, indexedBlockCheck (66688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66688 0 32 h0 checkBlocks_66688_66751_part0
  have h64 := extendCertifiedSegment 66688 32 32 h32 checkBlocks_66688_66751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66752_66815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66752_66815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66752_66815 :
    ∀ i : Fin 64, indexedBlockCheck (66752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66752 0 32 h0 checkBlocks_66752_66815_part0
  have h64 := extendCertifiedSegment 66752 32 32 h32 checkBlocks_66752_66815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66816_66879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66816_66879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66816_66879 :
    ∀ i : Fin 64, indexedBlockCheck (66816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66816 0 32 h0 checkBlocks_66816_66879_part0
  have h64 := extendCertifiedSegment 66816 32 32 h32 checkBlocks_66816_66879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66880_66943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66880_66943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66880_66943 :
    ∀ i : Fin 64, indexedBlockCheck (66880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66880 0 32 h0 checkBlocks_66880_66943_part0
  have h64 := extendCertifiedSegment 66880 32 32 h32 checkBlocks_66880_66943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66944_67007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (66944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66944_67007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (66976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66944_67007 :
    ∀ i : Fin 64, indexedBlockCheck (66944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 66944 0 32 h0 checkBlocks_66944_67007_part0
  have h64 := extendCertifiedSegment 66944 32 32 h32 checkBlocks_66944_67007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67008_67071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67008_67071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67008_67071 :
    ∀ i : Fin 64, indexedBlockCheck (67008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67008 0 32 h0 checkBlocks_67008_67071_part0
  have h64 := extendCertifiedSegment 67008 32 32 h32 checkBlocks_67008_67071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_66560_67071 :
    ∀ i : Fin 512, indexedBlockCheck (66560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66560 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 66560 0 64 h0 checkBlocks_66560_66623
  have h128 := extendCertifiedSegment 66560 64 64 h64 checkBlocks_66624_66687
  have h192 := extendCertifiedSegment 66560 128 64 h128 checkBlocks_66688_66751
  have h256 := extendCertifiedSegment 66560 192 64 h192 checkBlocks_66752_66815
  have h320 := extendCertifiedSegment 66560 256 64 h256 checkBlocks_66816_66879
  have h384 := extendCertifiedSegment 66560 320 64 h320 checkBlocks_66880_66943
  have h448 := extendCertifiedSegment 66560 384 64 h384 checkBlocks_66944_67007
  have h512 := extendCertifiedSegment 66560 448 64 h448 checkBlocks_67008_67071
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_67072_67135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67072_67135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67072_67135 :
    ∀ i : Fin 64, indexedBlockCheck (67072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67072 0 32 h0 checkBlocks_67072_67135_part0
  have h64 := extendCertifiedSegment 67072 32 32 h32 checkBlocks_67072_67135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67136_67199_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67136_67199_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67136_67199 :
    ∀ i : Fin 64, indexedBlockCheck (67136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67136 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67136 0 32 h0 checkBlocks_67136_67199_part0
  have h64 := extendCertifiedSegment 67136 32 32 h32 checkBlocks_67136_67199_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67200_67263_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67200_67263_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67200_67263 :
    ∀ i : Fin 64, indexedBlockCheck (67200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67200 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67200 0 32 h0 checkBlocks_67200_67263_part0
  have h64 := extendCertifiedSegment 67200 32 32 h32 checkBlocks_67200_67263_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67264_67327_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67264_67327_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67264_67327 :
    ∀ i : Fin 64, indexedBlockCheck (67264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67264 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67264 0 32 h0 checkBlocks_67264_67327_part0
  have h64 := extendCertifiedSegment 67264 32 32 h32 checkBlocks_67264_67327_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67328_67391_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67328_67391_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67328_67391 :
    ∀ i : Fin 64, indexedBlockCheck (67328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67328 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67328 0 32 h0 checkBlocks_67328_67391_part0
  have h64 := extendCertifiedSegment 67328 32 32 h32 checkBlocks_67328_67391_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67392_67455_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67392_67455_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67392_67455 :
    ∀ i : Fin 64, indexedBlockCheck (67392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67392 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67392 0 32 h0 checkBlocks_67392_67455_part0
  have h64 := extendCertifiedSegment 67392 32 32 h32 checkBlocks_67392_67455_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67456_67519_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67456_67519_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67456_67519 :
    ∀ i : Fin 64, indexedBlockCheck (67456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67456 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67456 0 32 h0 checkBlocks_67456_67519_part0
  have h64 := extendCertifiedSegment 67456 32 32 h32 checkBlocks_67456_67519_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67520_67583_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67520_67583_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67520_67583 :
    ∀ i : Fin 64, indexedBlockCheck (67520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67520 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67520 0 32 h0 checkBlocks_67520_67583_part0
  have h64 := extendCertifiedSegment 67520 32 32 h32 checkBlocks_67520_67583_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67072_67583 :
    ∀ i : Fin 512, indexedBlockCheck (67072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67072 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 67072 0 64 h0 checkBlocks_67072_67135
  have h128 := extendCertifiedSegment 67072 64 64 h64 checkBlocks_67136_67199
  have h192 := extendCertifiedSegment 67072 128 64 h128 checkBlocks_67200_67263
  have h256 := extendCertifiedSegment 67072 192 64 h192 checkBlocks_67264_67327
  have h320 := extendCertifiedSegment 67072 256 64 h256 checkBlocks_67328_67391
  have h384 := extendCertifiedSegment 67072 320 64 h320 checkBlocks_67392_67455
  have h448 := extendCertifiedSegment 67072 384 64 h384 checkBlocks_67456_67519
  have h512 := extendCertifiedSegment 67072 448 64 h448 checkBlocks_67520_67583
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_67584_67647_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67584_67647_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67584_67647 :
    ∀ i : Fin 64, indexedBlockCheck (67584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67584 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67584 0 32 h0 checkBlocks_67584_67647_part0
  have h64 := extendCertifiedSegment 67584 32 32 h32 checkBlocks_67584_67647_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67648_67711_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67648_67711_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67648_67711 :
    ∀ i : Fin 64, indexedBlockCheck (67648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67648 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67648 0 32 h0 checkBlocks_67648_67711_part0
  have h64 := extendCertifiedSegment 67648 32 32 h32 checkBlocks_67648_67711_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67712_67775_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67712_67775_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67712_67775 :
    ∀ i : Fin 64, indexedBlockCheck (67712 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67712 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67712 0 32 h0 checkBlocks_67712_67775_part0
  have h64 := extendCertifiedSegment 67712 32 32 h32 checkBlocks_67712_67775_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67776_67839_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67776_67839_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67776_67839 :
    ∀ i : Fin 64, indexedBlockCheck (67776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67776 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67776 0 32 h0 checkBlocks_67776_67839_part0
  have h64 := extendCertifiedSegment 67776 32 32 h32 checkBlocks_67776_67839_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67840_67903_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67840_67903_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67840_67903 :
    ∀ i : Fin 64, indexedBlockCheck (67840 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67840 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67840 0 32 h0 checkBlocks_67840_67903_part0
  have h64 := extendCertifiedSegment 67840 32 32 h32 checkBlocks_67840_67903_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67904_67967_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67904_67967_part1 :
    ∀ i : Fin 32, indexedBlockCheck (67936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67904_67967 :
    ∀ i : Fin 64, indexedBlockCheck (67904 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67904 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67904 0 32 h0 checkBlocks_67904_67967_part0
  have h64 := extendCertifiedSegment 67904 32 32 h32 checkBlocks_67904_67967_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67968_68031_part0 :
    ∀ i : Fin 32, indexedBlockCheck (67968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67968_68031_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67968_68031 :
    ∀ i : Fin 64, indexedBlockCheck (67968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67968 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 67968 0 32 h0 checkBlocks_67968_68031_part0
  have h64 := extendCertifiedSegment 67968 32 32 h32 checkBlocks_67968_68031_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_68032_68095_part0 :
    ∀ i : Fin 32, indexedBlockCheck (68032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68032_68095_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68032_68095 :
    ∀ i : Fin 64, indexedBlockCheck (68032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68032 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 68032 0 32 h0 checkBlocks_68032_68095_part0
  have h64 := extendCertifiedSegment 68032 32 32 h32 checkBlocks_68032_68095_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_67584_68095 :
    ∀ i : Fin 512, indexedBlockCheck (67584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67584 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 67584 0 64 h0 checkBlocks_67584_67647
  have h128 := extendCertifiedSegment 67584 64 64 h64 checkBlocks_67648_67711
  have h192 := extendCertifiedSegment 67584 128 64 h128 checkBlocks_67712_67775
  have h256 := extendCertifiedSegment 67584 192 64 h192 checkBlocks_67776_67839
  have h320 := extendCertifiedSegment 67584 256 64 h256 checkBlocks_67840_67903
  have h384 := extendCertifiedSegment 67584 320 64 h320 checkBlocks_67904_67967
  have h448 := extendCertifiedSegment 67584 384 64 h384 checkBlocks_67968_68031
  have h512 := extendCertifiedSegment 67584 448 64 h448 checkBlocks_68032_68095
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_68096_68159_part0 :
    ∀ i : Fin 32, indexedBlockCheck (68096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68096_68159_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68096_68159 :
    ∀ i : Fin 64, indexedBlockCheck (68096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68096 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 68096 0 32 h0 checkBlocks_68096_68159_part0
  have h64 := extendCertifiedSegment 68096 32 32 h32 checkBlocks_68096_68159_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_68160_68223_part0 :
    ∀ i : Fin 32, indexedBlockCheck (68160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68160_68223_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68160_68223 :
    ∀ i : Fin 64, indexedBlockCheck (68160 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68160 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 68160 0 32 h0 checkBlocks_68160_68223_part0
  have h64 := extendCertifiedSegment 68160 32 32 h32 checkBlocks_68160_68223_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_68224_68287_part0 :
    ∀ i : Fin 32, indexedBlockCheck (68224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68224_68287_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68224_68287 :
    ∀ i : Fin 64, indexedBlockCheck (68224 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68224 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 68224 0 32 h0 checkBlocks_68224_68287_part0
  have h64 := extendCertifiedSegment 68224 32 32 h32 checkBlocks_68224_68287_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_68288_68351_part0 :
    ∀ i : Fin 32, indexedBlockCheck (68288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68288_68351_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68288_68351 :
    ∀ i : Fin 64, indexedBlockCheck (68288 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68288 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 68288 0 32 h0 checkBlocks_68288_68351_part0
  have h64 := extendCertifiedSegment 68288 32 32 h32 checkBlocks_68288_68351_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_68352_68415_part0 :
    ∀ i : Fin 32, indexedBlockCheck (68352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68352_68415_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68352_68415 :
    ∀ i : Fin 64, indexedBlockCheck (68352 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68352 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 68352 0 32 h0 checkBlocks_68352_68415_part0
  have h64 := extendCertifiedSegment 68352 32 32 h32 checkBlocks_68352_68415_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_68416_68479_part0 :
    ∀ i : Fin 32, indexedBlockCheck (68416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68416_68479_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68416_68479 :
    ∀ i : Fin 64, indexedBlockCheck (68416 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68416 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 68416 0 32 h0 checkBlocks_68416_68479_part0
  have h64 := extendCertifiedSegment 68416 32 32 h32 checkBlocks_68416_68479_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_68480_68543_part0 :
    ∀ i : Fin 32, indexedBlockCheck (68480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68480_68543_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68480_68543 :
    ∀ i : Fin 64, indexedBlockCheck (68480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68480 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 68480 0 32 h0 checkBlocks_68480_68543_part0
  have h64 := extendCertifiedSegment 68480 32 32 h32 checkBlocks_68480_68543_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_68544_68607_part0 :
    ∀ i : Fin 32, indexedBlockCheck (68544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68544_68607_part1 :
    ∀ i : Fin 32, indexedBlockCheck (68576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68544_68607 :
    ∀ i : Fin 64, indexedBlockCheck (68544 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68544 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 68544 0 32 h0 checkBlocks_68544_68607_part0
  have h64 := extendCertifiedSegment 68544 32 32 h32 checkBlocks_68544_68607_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_68096_68607 :
    ∀ i : Fin 512, indexedBlockCheck (68096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68096 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 68096 0 64 h0 checkBlocks_68096_68159
  have h128 := extendCertifiedSegment 68096 64 64 h64 checkBlocks_68160_68223
  have h192 := extendCertifiedSegment 68096 128 64 h128 checkBlocks_68224_68287
  have h256 := extendCertifiedSegment 68096 192 64 h192 checkBlocks_68288_68351
  have h320 := extendCertifiedSegment 68096 256 64 h256 checkBlocks_68352_68415
  have h384 := extendCertifiedSegment 68096 320 64 h320 checkBlocks_68416_68479
  have h448 := extendCertifiedSegment 68096 384 64 h384 checkBlocks_68480_68543
  have h512 := extendCertifiedSegment 68096 448 64 h448 checkBlocks_68544_68607
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [66560, 68608) passes the packed checker. -/
public theorem blocks_in_66560_68608 :
    ∀ i : Fin 2048, indexedBlockCheck (66560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66560 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 66560 0 512 h0 checkBlocks_66560_67071
  have h1024 := extendCertifiedSegment 66560 512 512 h512 checkBlocks_67072_67583
  have h1536 := extendCertifiedSegment 66560 1024 512 h1024 checkBlocks_67584_68095
  have h2048 := extendCertifiedSegment 66560 1536 512 h1536 checkBlocks_68096_68607
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
