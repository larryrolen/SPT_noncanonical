/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 3072 through 5119 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_3072_3135 :
    ∀ i : Fin 64, indexedBlockCheck (3072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3136_3199 :
    ∀ i : Fin 64, indexedBlockCheck (3136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3200_3263 :
    ∀ i : Fin 64, indexedBlockCheck (3200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3264_3327 :
    ∀ i : Fin 64, indexedBlockCheck (3264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3328_3391 :
    ∀ i : Fin 64, indexedBlockCheck (3328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3392_3455 :
    ∀ i : Fin 64, indexedBlockCheck (3392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3456_3519 :
    ∀ i : Fin 64, indexedBlockCheck (3456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3520_3583 :
    ∀ i : Fin 64, indexedBlockCheck (3520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3072_3583 :
    ∀ i : Fin 512, indexedBlockCheck (3072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (3072 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 3072 0 64 h0 checkBlocks_3072_3135
  have h128 := extendCertifiedSegment 3072 64 64 h64 checkBlocks_3136_3199
  have h192 := extendCertifiedSegment 3072 128 64 h128 checkBlocks_3200_3263
  have h256 := extendCertifiedSegment 3072 192 64 h192 checkBlocks_3264_3327
  have h320 := extendCertifiedSegment 3072 256 64 h256 checkBlocks_3328_3391
  have h384 := extendCertifiedSegment 3072 320 64 h320 checkBlocks_3392_3455
  have h448 := extendCertifiedSegment 3072 384 64 h384 checkBlocks_3456_3519
  have h512 := extendCertifiedSegment 3072 448 64 h448 checkBlocks_3520_3583
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_3584_3647 :
    ∀ i : Fin 64, indexedBlockCheck (3584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3648_3711 :
    ∀ i : Fin 64, indexedBlockCheck (3648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3712_3775 :
    ∀ i : Fin 64, indexedBlockCheck (3712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3776_3839 :
    ∀ i : Fin 64, indexedBlockCheck (3776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3840_3903 :
    ∀ i : Fin 64, indexedBlockCheck (3840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3904_3967 :
    ∀ i : Fin 64, indexedBlockCheck (3904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3968_4031 :
    ∀ i : Fin 64, indexedBlockCheck (3968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4032_4095 :
    ∀ i : Fin 64, indexedBlockCheck (4032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3584_4095 :
    ∀ i : Fin 512, indexedBlockCheck (3584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (3584 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 3584 0 64 h0 checkBlocks_3584_3647
  have h128 := extendCertifiedSegment 3584 64 64 h64 checkBlocks_3648_3711
  have h192 := extendCertifiedSegment 3584 128 64 h128 checkBlocks_3712_3775
  have h256 := extendCertifiedSegment 3584 192 64 h192 checkBlocks_3776_3839
  have h320 := extendCertifiedSegment 3584 256 64 h256 checkBlocks_3840_3903
  have h384 := extendCertifiedSegment 3584 320 64 h320 checkBlocks_3904_3967
  have h448 := extendCertifiedSegment 3584 384 64 h384 checkBlocks_3968_4031
  have h512 := extendCertifiedSegment 3584 448 64 h448 checkBlocks_4032_4095
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_4096_4159 :
    ∀ i : Fin 64, indexedBlockCheck (4096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4160_4223 :
    ∀ i : Fin 64, indexedBlockCheck (4160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4224_4287 :
    ∀ i : Fin 64, indexedBlockCheck (4224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4288_4351 :
    ∀ i : Fin 64, indexedBlockCheck (4288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4352_4415 :
    ∀ i : Fin 64, indexedBlockCheck (4352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4416_4479 :
    ∀ i : Fin 64, indexedBlockCheck (4416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4480_4543 :
    ∀ i : Fin 64, indexedBlockCheck (4480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4544_4607 :
    ∀ i : Fin 64, indexedBlockCheck (4544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4096_4607 :
    ∀ i : Fin 512, indexedBlockCheck (4096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (4096 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 4096 0 64 h0 checkBlocks_4096_4159
  have h128 := extendCertifiedSegment 4096 64 64 h64 checkBlocks_4160_4223
  have h192 := extendCertifiedSegment 4096 128 64 h128 checkBlocks_4224_4287
  have h256 := extendCertifiedSegment 4096 192 64 h192 checkBlocks_4288_4351
  have h320 := extendCertifiedSegment 4096 256 64 h256 checkBlocks_4352_4415
  have h384 := extendCertifiedSegment 4096 320 64 h320 checkBlocks_4416_4479
  have h448 := extendCertifiedSegment 4096 384 64 h384 checkBlocks_4480_4543
  have h512 := extendCertifiedSegment 4096 448 64 h448 checkBlocks_4544_4607
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_4608_4671 :
    ∀ i : Fin 64, indexedBlockCheck (4608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4672_4735 :
    ∀ i : Fin 64, indexedBlockCheck (4672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4736_4799 :
    ∀ i : Fin 64, indexedBlockCheck (4736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4800_4863 :
    ∀ i : Fin 64, indexedBlockCheck (4800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4864_4927 :
    ∀ i : Fin 64, indexedBlockCheck (4864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4928_4991 :
    ∀ i : Fin 64, indexedBlockCheck (4928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4992_5055 :
    ∀ i : Fin 64, indexedBlockCheck (4992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5056_5119 :
    ∀ i : Fin 64, indexedBlockCheck (5056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_4608_5119 :
    ∀ i : Fin 512, indexedBlockCheck (4608 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (4608 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 4608 0 64 h0 checkBlocks_4608_4671
  have h128 := extendCertifiedSegment 4608 64 64 h64 checkBlocks_4672_4735
  have h192 := extendCertifiedSegment 4608 128 64 h128 checkBlocks_4736_4799
  have h256 := extendCertifiedSegment 4608 192 64 h192 checkBlocks_4800_4863
  have h320 := extendCertifiedSegment 4608 256 64 h256 checkBlocks_4864_4927
  have h384 := extendCertifiedSegment 4608 320 64 h320 checkBlocks_4928_4991
  have h448 := extendCertifiedSegment 4608 384 64 h384 checkBlocks_4992_5055
  have h512 := extendCertifiedSegment 4608 448 64 h448 checkBlocks_5056_5119
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [3072, 5120) passes the packed checker. -/
public theorem blocks_in_3072_5120 :
    ∀ i : Fin 2048, indexedBlockCheck (3072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (3072 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 3072 0 512 h0 checkBlocks_3072_3583
  have h1024 := extendCertifiedSegment 3072 512 512 h512 checkBlocks_3584_4095
  have h1536 := extendCertifiedSegment 3072 1024 512 h1024 checkBlocks_4096_4607
  have h2048 := extendCertifiedSegment 3072 1536 512 h1536 checkBlocks_4608_5119
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
