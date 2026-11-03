/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 74752 through 76799 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_74752_74815 :
    ∀ i : Fin 64, indexedBlockCheck (74752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74816_74879 :
    ∀ i : Fin 64, indexedBlockCheck (74816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74880_74943 :
    ∀ i : Fin 64, indexedBlockCheck (74880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74944_75007 :
    ∀ i : Fin 64, indexedBlockCheck (74944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75008_75071 :
    ∀ i : Fin 64, indexedBlockCheck (75008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75072_75135 :
    ∀ i : Fin 64, indexedBlockCheck (75072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75136_75199 :
    ∀ i : Fin 64, indexedBlockCheck (75136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75200_75263 :
    ∀ i : Fin 64, indexedBlockCheck (75200 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_75264_75327 :
    ∀ i : Fin 64, indexedBlockCheck (75264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75328_75391 :
    ∀ i : Fin 64, indexedBlockCheck (75328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75392_75455 :
    ∀ i : Fin 64, indexedBlockCheck (75392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75456_75519 :
    ∀ i : Fin 64, indexedBlockCheck (75456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75520_75583 :
    ∀ i : Fin 64, indexedBlockCheck (75520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75584_75647 :
    ∀ i : Fin 64, indexedBlockCheck (75584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75648_75711 :
    ∀ i : Fin 64, indexedBlockCheck (75648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75712_75775 :
    ∀ i : Fin 64, indexedBlockCheck (75712 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_75776_75839 :
    ∀ i : Fin 64, indexedBlockCheck (75776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75840_75903 :
    ∀ i : Fin 64, indexedBlockCheck (75840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75904_75967 :
    ∀ i : Fin 64, indexedBlockCheck (75904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_75968_76031 :
    ∀ i : Fin 64, indexedBlockCheck (75968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76032_76095 :
    ∀ i : Fin 64, indexedBlockCheck (76032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76096_76159 :
    ∀ i : Fin 64, indexedBlockCheck (76096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76160_76223 :
    ∀ i : Fin 64, indexedBlockCheck (76160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76224_76287 :
    ∀ i : Fin 64, indexedBlockCheck (76224 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_76288_76351 :
    ∀ i : Fin 64, indexedBlockCheck (76288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76352_76415 :
    ∀ i : Fin 64, indexedBlockCheck (76352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76416_76479 :
    ∀ i : Fin 64, indexedBlockCheck (76416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76480_76543 :
    ∀ i : Fin 64, indexedBlockCheck (76480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76544_76607 :
    ∀ i : Fin 64, indexedBlockCheck (76544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76608_76671 :
    ∀ i : Fin 64, indexedBlockCheck (76608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76672_76735 :
    ∀ i : Fin 64, indexedBlockCheck (76672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76736_76799 :
    ∀ i : Fin 64, indexedBlockCheck (76736 + i.val) = true := by
  decide +kernel

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
