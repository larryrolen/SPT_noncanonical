/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 7168 through 9215 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_7168_7231 :
    ∀ i : Fin 64, indexedBlockCheck (7168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7232_7295 :
    ∀ i : Fin 64, indexedBlockCheck (7232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7296_7359 :
    ∀ i : Fin 64, indexedBlockCheck (7296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7360_7423 :
    ∀ i : Fin 64, indexedBlockCheck (7360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7424_7487 :
    ∀ i : Fin 64, indexedBlockCheck (7424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7488_7551 :
    ∀ i : Fin 64, indexedBlockCheck (7488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7552_7615 :
    ∀ i : Fin 64, indexedBlockCheck (7552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7616_7679 :
    ∀ i : Fin 64, indexedBlockCheck (7616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7168_7679 :
    ∀ i : Fin 512, indexedBlockCheck (7168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7168 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 7168 0 64 h0 checkBlocks_7168_7231
  have h128 := extendCertifiedSegment 7168 64 64 h64 checkBlocks_7232_7295
  have h192 := extendCertifiedSegment 7168 128 64 h128 checkBlocks_7296_7359
  have h256 := extendCertifiedSegment 7168 192 64 h192 checkBlocks_7360_7423
  have h320 := extendCertifiedSegment 7168 256 64 h256 checkBlocks_7424_7487
  have h384 := extendCertifiedSegment 7168 320 64 h320 checkBlocks_7488_7551
  have h448 := extendCertifiedSegment 7168 384 64 h384 checkBlocks_7552_7615
  have h512 := extendCertifiedSegment 7168 448 64 h448 checkBlocks_7616_7679
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_7680_7743 :
    ∀ i : Fin 64, indexedBlockCheck (7680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7744_7807 :
    ∀ i : Fin 64, indexedBlockCheck (7744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7808_7871 :
    ∀ i : Fin 64, indexedBlockCheck (7808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7872_7935 :
    ∀ i : Fin 64, indexedBlockCheck (7872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7936_7999 :
    ∀ i : Fin 64, indexedBlockCheck (7936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8000_8063 :
    ∀ i : Fin 64, indexedBlockCheck (8000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8064_8127 :
    ∀ i : Fin 64, indexedBlockCheck (8064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8128_8191 :
    ∀ i : Fin 64, indexedBlockCheck (8128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7680_8191 :
    ∀ i : Fin 512, indexedBlockCheck (7680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7680 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 7680 0 64 h0 checkBlocks_7680_7743
  have h128 := extendCertifiedSegment 7680 64 64 h64 checkBlocks_7744_7807
  have h192 := extendCertifiedSegment 7680 128 64 h128 checkBlocks_7808_7871
  have h256 := extendCertifiedSegment 7680 192 64 h192 checkBlocks_7872_7935
  have h320 := extendCertifiedSegment 7680 256 64 h256 checkBlocks_7936_7999
  have h384 := extendCertifiedSegment 7680 320 64 h320 checkBlocks_8000_8063
  have h448 := extendCertifiedSegment 7680 384 64 h384 checkBlocks_8064_8127
  have h512 := extendCertifiedSegment 7680 448 64 h448 checkBlocks_8128_8191
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_8192_8255 :
    ∀ i : Fin 64, indexedBlockCheck (8192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8256_8319 :
    ∀ i : Fin 64, indexedBlockCheck (8256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8320_8383 :
    ∀ i : Fin 64, indexedBlockCheck (8320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8384_8447 :
    ∀ i : Fin 64, indexedBlockCheck (8384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8448_8511 :
    ∀ i : Fin 64, indexedBlockCheck (8448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8512_8575 :
    ∀ i : Fin 64, indexedBlockCheck (8512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8576_8639 :
    ∀ i : Fin 64, indexedBlockCheck (8576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8640_8703 :
    ∀ i : Fin 64, indexedBlockCheck (8640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8192_8703 :
    ∀ i : Fin 512, indexedBlockCheck (8192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8192 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 8192 0 64 h0 checkBlocks_8192_8255
  have h128 := extendCertifiedSegment 8192 64 64 h64 checkBlocks_8256_8319
  have h192 := extendCertifiedSegment 8192 128 64 h128 checkBlocks_8320_8383
  have h256 := extendCertifiedSegment 8192 192 64 h192 checkBlocks_8384_8447
  have h320 := extendCertifiedSegment 8192 256 64 h256 checkBlocks_8448_8511
  have h384 := extendCertifiedSegment 8192 320 64 h320 checkBlocks_8512_8575
  have h448 := extendCertifiedSegment 8192 384 64 h384 checkBlocks_8576_8639
  have h512 := extendCertifiedSegment 8192 448 64 h448 checkBlocks_8640_8703
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_8704_8767 :
    ∀ i : Fin 64, indexedBlockCheck (8704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8768_8831 :
    ∀ i : Fin 64, indexedBlockCheck (8768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8832_8895 :
    ∀ i : Fin 64, indexedBlockCheck (8832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8896_8959 :
    ∀ i : Fin 64, indexedBlockCheck (8896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8960_9023 :
    ∀ i : Fin 64, indexedBlockCheck (8960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9024_9087 :
    ∀ i : Fin 64, indexedBlockCheck (9024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9088_9151 :
    ∀ i : Fin 64, indexedBlockCheck (9088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9152_9215 :
    ∀ i : Fin 64, indexedBlockCheck (9152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8704_9215 :
    ∀ i : Fin 512, indexedBlockCheck (8704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8704 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 8704 0 64 h0 checkBlocks_8704_8767
  have h128 := extendCertifiedSegment 8704 64 64 h64 checkBlocks_8768_8831
  have h192 := extendCertifiedSegment 8704 128 64 h128 checkBlocks_8832_8895
  have h256 := extendCertifiedSegment 8704 192 64 h192 checkBlocks_8896_8959
  have h320 := extendCertifiedSegment 8704 256 64 h256 checkBlocks_8960_9023
  have h384 := extendCertifiedSegment 8704 320 64 h320 checkBlocks_9024_9087
  have h448 := extendCertifiedSegment 8704 384 64 h384 checkBlocks_9088_9151
  have h512 := extendCertifiedSegment 8704 448 64 h448 checkBlocks_9152_9215
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [7168, 9216) passes the packed checker. -/
public theorem blocks_in_7168_9216 :
    ∀ i : Fin 2048, indexedBlockCheck (7168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7168 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 7168 0 512 h0 checkBlocks_7168_7679
  have h1024 := extendCertifiedSegment 7168 512 512 h512 checkBlocks_7680_8191
  have h1536 := extendCertifiedSegment 7168 1024 512 h1024 checkBlocks_8192_8703
  have h2048 := extendCertifiedSegment 7168 1536 512 h1536 checkBlocks_8704_9215
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
