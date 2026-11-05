/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 7168 through 9215 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_7168_7231_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7168_7231_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7168_7231 :
    ∀ i : Fin 64, indexedBlockCheck (7168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7168 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7168 0 32 h0 checkBlocks_7168_7231_part0
  have h64 := extendCertifiedSegment 7168 32 32 h32 checkBlocks_7168_7231_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7232_7295_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7232_7295_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7232_7295 :
    ∀ i : Fin 64, indexedBlockCheck (7232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7232 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7232 0 32 h0 checkBlocks_7232_7295_part0
  have h64 := extendCertifiedSegment 7232 32 32 h32 checkBlocks_7232_7295_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7296_7359_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7296_7359_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7296_7359 :
    ∀ i : Fin 64, indexedBlockCheck (7296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7296 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7296 0 32 h0 checkBlocks_7296_7359_part0
  have h64 := extendCertifiedSegment 7296 32 32 h32 checkBlocks_7296_7359_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7360_7423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7360_7423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7360_7423 :
    ∀ i : Fin 64, indexedBlockCheck (7360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7360 0 32 h0 checkBlocks_7360_7423_part0
  have h64 := extendCertifiedSegment 7360 32 32 h32 checkBlocks_7360_7423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7424_7487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7424_7487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7424_7487 :
    ∀ i : Fin 64, indexedBlockCheck (7424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7424 0 32 h0 checkBlocks_7424_7487_part0
  have h64 := extendCertifiedSegment 7424 32 32 h32 checkBlocks_7424_7487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7488_7551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7488_7551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7488_7551 :
    ∀ i : Fin 64, indexedBlockCheck (7488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7488 0 32 h0 checkBlocks_7488_7551_part0
  have h64 := extendCertifiedSegment 7488 32 32 h32 checkBlocks_7488_7551_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7552_7615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7552_7615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7552_7615 :
    ∀ i : Fin 64, indexedBlockCheck (7552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7552 0 32 h0 checkBlocks_7552_7615_part0
  have h64 := extendCertifiedSegment 7552 32 32 h32 checkBlocks_7552_7615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7616_7679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7616_7679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7616_7679 :
    ∀ i : Fin 64, indexedBlockCheck (7616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7616 0 32 h0 checkBlocks_7616_7679_part0
  have h64 := extendCertifiedSegment 7616 32 32 h32 checkBlocks_7616_7679_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_7680_7743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7680_7743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7680_7743 :
    ∀ i : Fin 64, indexedBlockCheck (7680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7680 0 32 h0 checkBlocks_7680_7743_part0
  have h64 := extendCertifiedSegment 7680 32 32 h32 checkBlocks_7680_7743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7744_7807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7744_7807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7744_7807 :
    ∀ i : Fin 64, indexedBlockCheck (7744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7744 0 32 h0 checkBlocks_7744_7807_part0
  have h64 := extendCertifiedSegment 7744 32 32 h32 checkBlocks_7744_7807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7808_7871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7808_7871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7808_7871 :
    ∀ i : Fin 64, indexedBlockCheck (7808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7808 0 32 h0 checkBlocks_7808_7871_part0
  have h64 := extendCertifiedSegment 7808 32 32 h32 checkBlocks_7808_7871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7872_7935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7872_7935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7872_7935 :
    ∀ i : Fin 64, indexedBlockCheck (7872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7872 0 32 h0 checkBlocks_7872_7935_part0
  have h64 := extendCertifiedSegment 7872 32 32 h32 checkBlocks_7872_7935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7936_7999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7936_7999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7936_7999 :
    ∀ i : Fin 64, indexedBlockCheck (7936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7936 0 32 h0 checkBlocks_7936_7999_part0
  have h64 := extendCertifiedSegment 7936 32 32 h32 checkBlocks_7936_7999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8000_8063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8000_8063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8000_8063 :
    ∀ i : Fin 64, indexedBlockCheck (8000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8000 0 32 h0 checkBlocks_8000_8063_part0
  have h64 := extendCertifiedSegment 8000 32 32 h32 checkBlocks_8000_8063_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8064_8127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8064_8127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8064_8127 :
    ∀ i : Fin 64, indexedBlockCheck (8064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8064 0 32 h0 checkBlocks_8064_8127_part0
  have h64 := extendCertifiedSegment 8064 32 32 h32 checkBlocks_8064_8127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8128_8191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8128_8191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8128_8191 :
    ∀ i : Fin 64, indexedBlockCheck (8128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8128 0 32 h0 checkBlocks_8128_8191_part0
  have h64 := extendCertifiedSegment 8128 32 32 h32 checkBlocks_8128_8191_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_8192_8255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8192_8255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8192_8255 :
    ∀ i : Fin 64, indexedBlockCheck (8192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8192 0 32 h0 checkBlocks_8192_8255_part0
  have h64 := extendCertifiedSegment 8192 32 32 h32 checkBlocks_8192_8255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8256_8319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8256_8319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8256_8319 :
    ∀ i : Fin 64, indexedBlockCheck (8256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8256 0 32 h0 checkBlocks_8256_8319_part0
  have h64 := extendCertifiedSegment 8256 32 32 h32 checkBlocks_8256_8319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8320_8383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8320_8383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8320_8383 :
    ∀ i : Fin 64, indexedBlockCheck (8320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8320 0 32 h0 checkBlocks_8320_8383_part0
  have h64 := extendCertifiedSegment 8320 32 32 h32 checkBlocks_8320_8383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8384_8447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8384_8447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8384_8447 :
    ∀ i : Fin 64, indexedBlockCheck (8384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8384 0 32 h0 checkBlocks_8384_8447_part0
  have h64 := extendCertifiedSegment 8384 32 32 h32 checkBlocks_8384_8447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8448_8511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8448_8511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8448_8511 :
    ∀ i : Fin 64, indexedBlockCheck (8448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8448 0 32 h0 checkBlocks_8448_8511_part0
  have h64 := extendCertifiedSegment 8448 32 32 h32 checkBlocks_8448_8511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8512_8575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8512_8575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8512_8575 :
    ∀ i : Fin 64, indexedBlockCheck (8512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8512 0 32 h0 checkBlocks_8512_8575_part0
  have h64 := extendCertifiedSegment 8512 32 32 h32 checkBlocks_8512_8575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8576_8639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8576_8639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8576_8639 :
    ∀ i : Fin 64, indexedBlockCheck (8576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8576 0 32 h0 checkBlocks_8576_8639_part0
  have h64 := extendCertifiedSegment 8576 32 32 h32 checkBlocks_8576_8639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8640_8703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8640_8703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8640_8703 :
    ∀ i : Fin 64, indexedBlockCheck (8640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8640 0 32 h0 checkBlocks_8640_8703_part0
  have h64 := extendCertifiedSegment 8640 32 32 h32 checkBlocks_8640_8703_part1
  intro i
  exact h64 i.val i.isLt

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

private theorem checkBlocks_8704_8767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8704_8767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8704_8767 :
    ∀ i : Fin 64, indexedBlockCheck (8704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8704 0 32 h0 checkBlocks_8704_8767_part0
  have h64 := extendCertifiedSegment 8704 32 32 h32 checkBlocks_8704_8767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8768_8831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8768_8831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8768_8831 :
    ∀ i : Fin 64, indexedBlockCheck (8768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8768 0 32 h0 checkBlocks_8768_8831_part0
  have h64 := extendCertifiedSegment 8768 32 32 h32 checkBlocks_8768_8831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8832_8895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8832_8895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8832_8895 :
    ∀ i : Fin 64, indexedBlockCheck (8832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8832 0 32 h0 checkBlocks_8832_8895_part0
  have h64 := extendCertifiedSegment 8832 32 32 h32 checkBlocks_8832_8895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8896_8959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8896_8959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8896_8959 :
    ∀ i : Fin 64, indexedBlockCheck (8896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8896 0 32 h0 checkBlocks_8896_8959_part0
  have h64 := extendCertifiedSegment 8896 32 32 h32 checkBlocks_8896_8959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_8960_9023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (8960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8960_9023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (8992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_8960_9023 :
    ∀ i : Fin 64, indexedBlockCheck (8960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (8960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 8960 0 32 h0 checkBlocks_8960_9023_part0
  have h64 := extendCertifiedSegment 8960 32 32 h32 checkBlocks_8960_9023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9024_9087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9024_9087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9024_9087 :
    ∀ i : Fin 64, indexedBlockCheck (9024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9024 0 32 h0 checkBlocks_9024_9087_part0
  have h64 := extendCertifiedSegment 9024 32 32 h32 checkBlocks_9024_9087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9088_9151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9088_9151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9088_9151 :
    ∀ i : Fin 64, indexedBlockCheck (9088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9088 0 32 h0 checkBlocks_9088_9151_part0
  have h64 := extendCertifiedSegment 9088 32 32 h32 checkBlocks_9088_9151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9152_9215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9152_9215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9152_9215 :
    ∀ i : Fin 64, indexedBlockCheck (9152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9152 0 32 h0 checkBlocks_9152_9215_part0
  have h64 := extendCertifiedSegment 9152 32 32 h32 checkBlocks_9152_9215_part1
  intro i
  exact h64 i.val i.isLt

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
