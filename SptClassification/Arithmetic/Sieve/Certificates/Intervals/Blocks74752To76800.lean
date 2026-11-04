/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 74752 through 76799 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_74752_74815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74752_74815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74752_74815 :
    ∀ i : Fin 64, indexedBlockCheck (74752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74752 0 32 h0 checkBlocks_74752_74815_part0
  have h64 := extendCertifiedSegment 74752 32 32 h32 checkBlocks_74752_74815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74816_74879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74816_74879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74816_74879 :
    ∀ i : Fin 64, indexedBlockCheck (74816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74816 0 32 h0 checkBlocks_74816_74879_part0
  have h64 := extendCertifiedSegment 74816 32 32 h32 checkBlocks_74816_74879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74880_74943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74880_74943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74880_74943 :
    ∀ i : Fin 64, indexedBlockCheck (74880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74880 0 32 h0 checkBlocks_74880_74943_part0
  have h64 := extendCertifiedSegment 74880 32 32 h32 checkBlocks_74880_74943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74944_75007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74944_75007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74944_75007 :
    ∀ i : Fin 64, indexedBlockCheck (74944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74944 0 32 h0 checkBlocks_74944_75007_part0
  have h64 := extendCertifiedSegment 74944 32 32 h32 checkBlocks_74944_75007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75008_75071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75008_75071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75008_75071 :
    ∀ i : Fin 64, indexedBlockCheck (75008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75008 0 32 h0 checkBlocks_75008_75071_part0
  have h64 := extendCertifiedSegment 75008 32 32 h32 checkBlocks_75008_75071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75072_75135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75072_75135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75072_75135 :
    ∀ i : Fin 64, indexedBlockCheck (75072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75072 0 32 h0 checkBlocks_75072_75135_part0
  have h64 := extendCertifiedSegment 75072 32 32 h32 checkBlocks_75072_75135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75136_75199_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75136_75199_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75136_75199 :
    ∀ i : Fin 64, indexedBlockCheck (75136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75136 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75136 0 32 h0 checkBlocks_75136_75199_part0
  have h64 := extendCertifiedSegment 75136 32 32 h32 checkBlocks_75136_75199_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75200_75263_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75200_75263_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75200_75263 :
    ∀ i : Fin 64, indexedBlockCheck (75200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75200 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75200 0 32 h0 checkBlocks_75200_75263_part0
  have h64 := extendCertifiedSegment 75200 32 32 h32 checkBlocks_75200_75263_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74752_75263 :
    ∀ i : Fin 512, indexedBlockCheck (74752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74752 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 74752 0 64 h0 checkBlocks_74752_74815
  have h128 := extendCertifiedSegment 74752 64 64 h64 checkBlocks_74816_74879
  have h192 := extendCertifiedSegment 74752 128 64 h128 checkBlocks_74880_74943
  have h256 := extendCertifiedSegment 74752 192 64 h192 checkBlocks_74944_75007
  have h320 := extendCertifiedSegment 74752 256 64 h256 checkBlocks_75008_75071
  have h384 := extendCertifiedSegment 74752 320 64 h320 checkBlocks_75072_75135
  have h448 := extendCertifiedSegment 74752 384 64 h384 checkBlocks_75136_75199
  have h512 := extendCertifiedSegment 74752 448 64 h448 checkBlocks_75200_75263
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_75264_75327_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75264_75327_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75264_75327 :
    ∀ i : Fin 64, indexedBlockCheck (75264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75264 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75264 0 32 h0 checkBlocks_75264_75327_part0
  have h64 := extendCertifiedSegment 75264 32 32 h32 checkBlocks_75264_75327_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75328_75391_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75328_75391_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75328_75391 :
    ∀ i : Fin 64, indexedBlockCheck (75328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75328 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75328 0 32 h0 checkBlocks_75328_75391_part0
  have h64 := extendCertifiedSegment 75328 32 32 h32 checkBlocks_75328_75391_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75392_75455_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75392_75455_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75392_75455 :
    ∀ i : Fin 64, indexedBlockCheck (75392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75392 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75392 0 32 h0 checkBlocks_75392_75455_part0
  have h64 := extendCertifiedSegment 75392 32 32 h32 checkBlocks_75392_75455_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75456_75519_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75456_75519_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75456_75519 :
    ∀ i : Fin 64, indexedBlockCheck (75456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75456 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75456 0 32 h0 checkBlocks_75456_75519_part0
  have h64 := extendCertifiedSegment 75456 32 32 h32 checkBlocks_75456_75519_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75520_75583_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75520_75583_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75520_75583 :
    ∀ i : Fin 64, indexedBlockCheck (75520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75520 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75520 0 32 h0 checkBlocks_75520_75583_part0
  have h64 := extendCertifiedSegment 75520 32 32 h32 checkBlocks_75520_75583_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75584_75647_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75584_75647_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75584_75647 :
    ∀ i : Fin 64, indexedBlockCheck (75584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75584 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75584 0 32 h0 checkBlocks_75584_75647_part0
  have h64 := extendCertifiedSegment 75584 32 32 h32 checkBlocks_75584_75647_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75648_75711_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75648_75711_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75648_75711 :
    ∀ i : Fin 64, indexedBlockCheck (75648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75648 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75648 0 32 h0 checkBlocks_75648_75711_part0
  have h64 := extendCertifiedSegment 75648 32 32 h32 checkBlocks_75648_75711_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75712_75775_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75712_75775_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75712_75775 :
    ∀ i : Fin 64, indexedBlockCheck (75712 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75712 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75712 0 32 h0 checkBlocks_75712_75775_part0
  have h64 := extendCertifiedSegment 75712 32 32 h32 checkBlocks_75712_75775_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75264_75775 :
    ∀ i : Fin 512, indexedBlockCheck (75264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75264 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 75264 0 64 h0 checkBlocks_75264_75327
  have h128 := extendCertifiedSegment 75264 64 64 h64 checkBlocks_75328_75391
  have h192 := extendCertifiedSegment 75264 128 64 h128 checkBlocks_75392_75455
  have h256 := extendCertifiedSegment 75264 192 64 h192 checkBlocks_75456_75519
  have h320 := extendCertifiedSegment 75264 256 64 h256 checkBlocks_75520_75583
  have h384 := extendCertifiedSegment 75264 320 64 h320 checkBlocks_75584_75647
  have h448 := extendCertifiedSegment 75264 384 64 h384 checkBlocks_75648_75711
  have h512 := extendCertifiedSegment 75264 448 64 h448 checkBlocks_75712_75775
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_75776_75839_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75776_75839_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75776_75839 :
    ∀ i : Fin 64, indexedBlockCheck (75776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75776 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75776 0 32 h0 checkBlocks_75776_75839_part0
  have h64 := extendCertifiedSegment 75776 32 32 h32 checkBlocks_75776_75839_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75840_75903_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75840_75903_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75840_75903 :
    ∀ i : Fin 64, indexedBlockCheck (75840 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75840 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75840 0 32 h0 checkBlocks_75840_75903_part0
  have h64 := extendCertifiedSegment 75840 32 32 h32 checkBlocks_75840_75903_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75904_75967_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75904_75967_part1 :
    ∀ i : Fin 32, indexedBlockCheck (75936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75904_75967 :
    ∀ i : Fin 64, indexedBlockCheck (75904 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75904 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75904 0 32 h0 checkBlocks_75904_75967_part0
  have h64 := extendCertifiedSegment 75904 32 32 h32 checkBlocks_75904_75967_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75968_76031_part0 :
    ∀ i : Fin 32, indexedBlockCheck (75968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75968_76031_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75968_76031 :
    ∀ i : Fin 64, indexedBlockCheck (75968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75968 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 75968 0 32 h0 checkBlocks_75968_76031_part0
  have h64 := extendCertifiedSegment 75968 32 32 h32 checkBlocks_75968_76031_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76032_76095_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76032_76095_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76032_76095 :
    ∀ i : Fin 64, indexedBlockCheck (76032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76032 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76032 0 32 h0 checkBlocks_76032_76095_part0
  have h64 := extendCertifiedSegment 76032 32 32 h32 checkBlocks_76032_76095_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76096_76159_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76096_76159_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76096_76159 :
    ∀ i : Fin 64, indexedBlockCheck (76096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76096 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76096 0 32 h0 checkBlocks_76096_76159_part0
  have h64 := extendCertifiedSegment 76096 32 32 h32 checkBlocks_76096_76159_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76160_76223_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76160_76223_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76160_76223 :
    ∀ i : Fin 64, indexedBlockCheck (76160 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76160 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76160 0 32 h0 checkBlocks_76160_76223_part0
  have h64 := extendCertifiedSegment 76160 32 32 h32 checkBlocks_76160_76223_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76224_76287_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76224_76287_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76224_76287 :
    ∀ i : Fin 64, indexedBlockCheck (76224 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76224 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76224 0 32 h0 checkBlocks_76224_76287_part0
  have h64 := extendCertifiedSegment 76224 32 32 h32 checkBlocks_76224_76287_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_75776_76287 :
    ∀ i : Fin 512, indexedBlockCheck (75776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (75776 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 75776 0 64 h0 checkBlocks_75776_75839
  have h128 := extendCertifiedSegment 75776 64 64 h64 checkBlocks_75840_75903
  have h192 := extendCertifiedSegment 75776 128 64 h128 checkBlocks_75904_75967
  have h256 := extendCertifiedSegment 75776 192 64 h192 checkBlocks_75968_76031
  have h320 := extendCertifiedSegment 75776 256 64 h256 checkBlocks_76032_76095
  have h384 := extendCertifiedSegment 75776 320 64 h320 checkBlocks_76096_76159
  have h448 := extendCertifiedSegment 75776 384 64 h384 checkBlocks_76160_76223
  have h512 := extendCertifiedSegment 75776 448 64 h448 checkBlocks_76224_76287
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_76288_76351_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76288_76351_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76288_76351 :
    ∀ i : Fin 64, indexedBlockCheck (76288 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76288 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76288 0 32 h0 checkBlocks_76288_76351_part0
  have h64 := extendCertifiedSegment 76288 32 32 h32 checkBlocks_76288_76351_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76352_76415_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76352_76415_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76352_76415 :
    ∀ i : Fin 64, indexedBlockCheck (76352 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76352 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76352 0 32 h0 checkBlocks_76352_76415_part0
  have h64 := extendCertifiedSegment 76352 32 32 h32 checkBlocks_76352_76415_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76416_76479_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76416_76479_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76416_76479 :
    ∀ i : Fin 64, indexedBlockCheck (76416 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76416 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76416 0 32 h0 checkBlocks_76416_76479_part0
  have h64 := extendCertifiedSegment 76416 32 32 h32 checkBlocks_76416_76479_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76480_76543_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76480_76543_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76480_76543 :
    ∀ i : Fin 64, indexedBlockCheck (76480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76480 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76480 0 32 h0 checkBlocks_76480_76543_part0
  have h64 := extendCertifiedSegment 76480 32 32 h32 checkBlocks_76480_76543_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76544_76607_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76544_76607_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76544_76607 :
    ∀ i : Fin 64, indexedBlockCheck (76544 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76544 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76544 0 32 h0 checkBlocks_76544_76607_part0
  have h64 := extendCertifiedSegment 76544 32 32 h32 checkBlocks_76544_76607_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76608_76671_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76608_76671_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76608_76671 :
    ∀ i : Fin 64, indexedBlockCheck (76608 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76608 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76608 0 32 h0 checkBlocks_76608_76671_part0
  have h64 := extendCertifiedSegment 76608 32 32 h32 checkBlocks_76608_76671_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76672_76735_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76672_76735_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76672_76735 :
    ∀ i : Fin 64, indexedBlockCheck (76672 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76672 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76672 0 32 h0 checkBlocks_76672_76735_part0
  have h64 := extendCertifiedSegment 76672 32 32 h32 checkBlocks_76672_76735_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76736_76799_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76736_76799_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76736_76799 :
    ∀ i : Fin 64, indexedBlockCheck (76736 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76736 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76736 0 32 h0 checkBlocks_76736_76799_part0
  have h64 := extendCertifiedSegment 76736 32 32 h32 checkBlocks_76736_76799_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76288_76799 :
    ∀ i : Fin 512, indexedBlockCheck (76288 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76288 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 76288 0 64 h0 checkBlocks_76288_76351
  have h128 := extendCertifiedSegment 76288 64 64 h64 checkBlocks_76352_76415
  have h192 := extendCertifiedSegment 76288 128 64 h128 checkBlocks_76416_76479
  have h256 := extendCertifiedSegment 76288 192 64 h192 checkBlocks_76480_76543
  have h320 := extendCertifiedSegment 76288 256 64 h256 checkBlocks_76544_76607
  have h384 := extendCertifiedSegment 76288 320 64 h320 checkBlocks_76608_76671
  have h448 := extendCertifiedSegment 76288 384 64 h384 checkBlocks_76672_76735
  have h512 := extendCertifiedSegment 76288 448 64 h448 checkBlocks_76736_76799
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [74752, 76800) passes the packed checker. -/
public theorem blocks_in_74752_76800 :
    ∀ i : Fin 2048, indexedBlockCheck (74752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74752 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 74752 0 512 h0 checkBlocks_74752_75263
  have h1024 := extendCertifiedSegment 74752 512 512 h512 checkBlocks_75264_75775
  have h1536 := extendCertifiedSegment 74752 1024 512 h1024 checkBlocks_75776_76287
  have h2048 := extendCertifiedSegment 74752 1536 512 h1536 checkBlocks_76288_76799
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
