/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 15360 through 17407 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_15360_15423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15360_15423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15360_15423 :
    ∀ i : Fin 64, indexedBlockCheck (15360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15360 0 32 h0 checkBlocks_15360_15423_part0
  have h64 := extendCertifiedSegment 15360 32 32 h32 checkBlocks_15360_15423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15424_15487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15424_15487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15424_15487 :
    ∀ i : Fin 64, indexedBlockCheck (15424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15424 0 32 h0 checkBlocks_15424_15487_part0
  have h64 := extendCertifiedSegment 15424 32 32 h32 checkBlocks_15424_15487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15488_15551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15488_15551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15488_15551 :
    ∀ i : Fin 64, indexedBlockCheck (15488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15488 0 32 h0 checkBlocks_15488_15551_part0
  have h64 := extendCertifiedSegment 15488 32 32 h32 checkBlocks_15488_15551_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15552_15615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15552_15615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15552_15615 :
    ∀ i : Fin 64, indexedBlockCheck (15552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15552 0 32 h0 checkBlocks_15552_15615_part0
  have h64 := extendCertifiedSegment 15552 32 32 h32 checkBlocks_15552_15615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15616_15679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15616_15679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15616_15679 :
    ∀ i : Fin 64, indexedBlockCheck (15616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15616 0 32 h0 checkBlocks_15616_15679_part0
  have h64 := extendCertifiedSegment 15616 32 32 h32 checkBlocks_15616_15679_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15680_15743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15680_15743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15680_15743 :
    ∀ i : Fin 64, indexedBlockCheck (15680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15680 0 32 h0 checkBlocks_15680_15743_part0
  have h64 := extendCertifiedSegment 15680 32 32 h32 checkBlocks_15680_15743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15744_15807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15744_15807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15744_15807 :
    ∀ i : Fin 64, indexedBlockCheck (15744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15744 0 32 h0 checkBlocks_15744_15807_part0
  have h64 := extendCertifiedSegment 15744 32 32 h32 checkBlocks_15744_15807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15808_15871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15808_15871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15808_15871 :
    ∀ i : Fin 64, indexedBlockCheck (15808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15808 0 32 h0 checkBlocks_15808_15871_part0
  have h64 := extendCertifiedSegment 15808 32 32 h32 checkBlocks_15808_15871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15360_15871 :
    ∀ i : Fin 512, indexedBlockCheck (15360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15360 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 15360 0 64 h0 checkBlocks_15360_15423
  have h128 := extendCertifiedSegment 15360 64 64 h64 checkBlocks_15424_15487
  have h192 := extendCertifiedSegment 15360 128 64 h128 checkBlocks_15488_15551
  have h256 := extendCertifiedSegment 15360 192 64 h192 checkBlocks_15552_15615
  have h320 := extendCertifiedSegment 15360 256 64 h256 checkBlocks_15616_15679
  have h384 := extendCertifiedSegment 15360 320 64 h320 checkBlocks_15680_15743
  have h448 := extendCertifiedSegment 15360 384 64 h384 checkBlocks_15744_15807
  have h512 := extendCertifiedSegment 15360 448 64 h448 checkBlocks_15808_15871
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_15872_15935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15872_15935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15872_15935 :
    ∀ i : Fin 64, indexedBlockCheck (15872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15872 0 32 h0 checkBlocks_15872_15935_part0
  have h64 := extendCertifiedSegment 15872 32 32 h32 checkBlocks_15872_15935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15936_15999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (15936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15936_15999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (15968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15936_15999 :
    ∀ i : Fin 64, indexedBlockCheck (15936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 15936 0 32 h0 checkBlocks_15936_15999_part0
  have h64 := extendCertifiedSegment 15936 32 32 h32 checkBlocks_15936_15999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16000_16063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16000_16063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16000_16063 :
    ∀ i : Fin 64, indexedBlockCheck (16000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16000 0 32 h0 checkBlocks_16000_16063_part0
  have h64 := extendCertifiedSegment 16000 32 32 h32 checkBlocks_16000_16063_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16064_16127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16064_16127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16064_16127 :
    ∀ i : Fin 64, indexedBlockCheck (16064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16064 0 32 h0 checkBlocks_16064_16127_part0
  have h64 := extendCertifiedSegment 16064 32 32 h32 checkBlocks_16064_16127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16128_16191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16128_16191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16128_16191 :
    ∀ i : Fin 64, indexedBlockCheck (16128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16128 0 32 h0 checkBlocks_16128_16191_part0
  have h64 := extendCertifiedSegment 16128 32 32 h32 checkBlocks_16128_16191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16192_16255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16192_16255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16192_16255 :
    ∀ i : Fin 64, indexedBlockCheck (16192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16192 0 32 h0 checkBlocks_16192_16255_part0
  have h64 := extendCertifiedSegment 16192 32 32 h32 checkBlocks_16192_16255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16256_16319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16256_16319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16256_16319 :
    ∀ i : Fin 64, indexedBlockCheck (16256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16256 0 32 h0 checkBlocks_16256_16319_part0
  have h64 := extendCertifiedSegment 16256 32 32 h32 checkBlocks_16256_16319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16320_16383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16320_16383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16320_16383 :
    ∀ i : Fin 64, indexedBlockCheck (16320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16320 0 32 h0 checkBlocks_16320_16383_part0
  have h64 := extendCertifiedSegment 16320 32 32 h32 checkBlocks_16320_16383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_15872_16383 :
    ∀ i : Fin 512, indexedBlockCheck (15872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15872 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 15872 0 64 h0 checkBlocks_15872_15935
  have h128 := extendCertifiedSegment 15872 64 64 h64 checkBlocks_15936_15999
  have h192 := extendCertifiedSegment 15872 128 64 h128 checkBlocks_16000_16063
  have h256 := extendCertifiedSegment 15872 192 64 h192 checkBlocks_16064_16127
  have h320 := extendCertifiedSegment 15872 256 64 h256 checkBlocks_16128_16191
  have h384 := extendCertifiedSegment 15872 320 64 h320 checkBlocks_16192_16255
  have h448 := extendCertifiedSegment 15872 384 64 h384 checkBlocks_16256_16319
  have h512 := extendCertifiedSegment 15872 448 64 h448 checkBlocks_16320_16383
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_16384_16447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16384_16447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16384_16447 :
    ∀ i : Fin 64, indexedBlockCheck (16384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16384 0 32 h0 checkBlocks_16384_16447_part0
  have h64 := extendCertifiedSegment 16384 32 32 h32 checkBlocks_16384_16447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16448_16511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16448_16511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16448_16511 :
    ∀ i : Fin 64, indexedBlockCheck (16448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16448 0 32 h0 checkBlocks_16448_16511_part0
  have h64 := extendCertifiedSegment 16448 32 32 h32 checkBlocks_16448_16511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16512_16575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16512_16575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16512_16575 :
    ∀ i : Fin 64, indexedBlockCheck (16512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16512 0 32 h0 checkBlocks_16512_16575_part0
  have h64 := extendCertifiedSegment 16512 32 32 h32 checkBlocks_16512_16575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16576_16639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16576_16639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16576_16639 :
    ∀ i : Fin 64, indexedBlockCheck (16576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16576 0 32 h0 checkBlocks_16576_16639_part0
  have h64 := extendCertifiedSegment 16576 32 32 h32 checkBlocks_16576_16639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16640_16703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16640_16703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16640_16703 :
    ∀ i : Fin 64, indexedBlockCheck (16640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16640 0 32 h0 checkBlocks_16640_16703_part0
  have h64 := extendCertifiedSegment 16640 32 32 h32 checkBlocks_16640_16703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16704_16767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16704_16767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16704_16767 :
    ∀ i : Fin 64, indexedBlockCheck (16704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16704 0 32 h0 checkBlocks_16704_16767_part0
  have h64 := extendCertifiedSegment 16704 32 32 h32 checkBlocks_16704_16767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16768_16831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16768_16831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16768_16831 :
    ∀ i : Fin 64, indexedBlockCheck (16768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16768 0 32 h0 checkBlocks_16768_16831_part0
  have h64 := extendCertifiedSegment 16768 32 32 h32 checkBlocks_16768_16831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16832_16895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16832_16895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16832_16895 :
    ∀ i : Fin 64, indexedBlockCheck (16832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16832 0 32 h0 checkBlocks_16832_16895_part0
  have h64 := extendCertifiedSegment 16832 32 32 h32 checkBlocks_16832_16895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16384_16895 :
    ∀ i : Fin 512, indexedBlockCheck (16384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16384 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 16384 0 64 h0 checkBlocks_16384_16447
  have h128 := extendCertifiedSegment 16384 64 64 h64 checkBlocks_16448_16511
  have h192 := extendCertifiedSegment 16384 128 64 h128 checkBlocks_16512_16575
  have h256 := extendCertifiedSegment 16384 192 64 h192 checkBlocks_16576_16639
  have h320 := extendCertifiedSegment 16384 256 64 h256 checkBlocks_16640_16703
  have h384 := extendCertifiedSegment 16384 320 64 h320 checkBlocks_16704_16767
  have h448 := extendCertifiedSegment 16384 384 64 h384 checkBlocks_16768_16831
  have h512 := extendCertifiedSegment 16384 448 64 h448 checkBlocks_16832_16895
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_16896_16959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16896_16959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16896_16959 :
    ∀ i : Fin 64, indexedBlockCheck (16896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16896 0 32 h0 checkBlocks_16896_16959_part0
  have h64 := extendCertifiedSegment 16896 32 32 h32 checkBlocks_16896_16959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16960_17023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (16960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16960_17023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (16992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_16960_17023 :
    ∀ i : Fin 64, indexedBlockCheck (16960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 16960 0 32 h0 checkBlocks_16960_17023_part0
  have h64 := extendCertifiedSegment 16960 32 32 h32 checkBlocks_16960_17023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17024_17087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17024_17087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17024_17087 :
    ∀ i : Fin 64, indexedBlockCheck (17024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17024 0 32 h0 checkBlocks_17024_17087_part0
  have h64 := extendCertifiedSegment 17024 32 32 h32 checkBlocks_17024_17087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17088_17151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17088_17151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17088_17151 :
    ∀ i : Fin 64, indexedBlockCheck (17088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17088 0 32 h0 checkBlocks_17088_17151_part0
  have h64 := extendCertifiedSegment 17088 32 32 h32 checkBlocks_17088_17151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17152_17215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17152_17215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17152_17215 :
    ∀ i : Fin 64, indexedBlockCheck (17152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17152 0 32 h0 checkBlocks_17152_17215_part0
  have h64 := extendCertifiedSegment 17152 32 32 h32 checkBlocks_17152_17215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17216_17279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17216_17279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17216_17279 :
    ∀ i : Fin 64, indexedBlockCheck (17216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17216 0 32 h0 checkBlocks_17216_17279_part0
  have h64 := extendCertifiedSegment 17216 32 32 h32 checkBlocks_17216_17279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17280_17343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17280_17343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17280_17343 :
    ∀ i : Fin 64, indexedBlockCheck (17280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17280 0 32 h0 checkBlocks_17280_17343_part0
  have h64 := extendCertifiedSegment 17280 32 32 h32 checkBlocks_17280_17343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_17344_17407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (17344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17344_17407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (17376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_17344_17407 :
    ∀ i : Fin 64, indexedBlockCheck (17344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (17344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 17344 0 32 h0 checkBlocks_17344_17407_part0
  have h64 := extendCertifiedSegment 17344 32 32 h32 checkBlocks_17344_17407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_16896_17407 :
    ∀ i : Fin 512, indexedBlockCheck (16896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (16896 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 16896 0 64 h0 checkBlocks_16896_16959
  have h128 := extendCertifiedSegment 16896 64 64 h64 checkBlocks_16960_17023
  have h192 := extendCertifiedSegment 16896 128 64 h128 checkBlocks_17024_17087
  have h256 := extendCertifiedSegment 16896 192 64 h192 checkBlocks_17088_17151
  have h320 := extendCertifiedSegment 16896 256 64 h256 checkBlocks_17152_17215
  have h384 := extendCertifiedSegment 16896 320 64 h320 checkBlocks_17216_17279
  have h448 := extendCertifiedSegment 16896 384 64 h384 checkBlocks_17280_17343
  have h512 := extendCertifiedSegment 16896 448 64 h448 checkBlocks_17344_17407
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [15360, 17408) passes the packed checker. -/
public theorem blocks_in_15360_17408 :
    ∀ i : Fin 2048, indexedBlockCheck (15360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (15360 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 15360 0 512 h0 checkBlocks_15360_15871
  have h1024 := extendCertifiedSegment 15360 512 512 h512 checkBlocks_15872_16383
  have h1536 := extendCertifiedSegment 15360 1024 512 h1024 checkBlocks_16384_16895
  have h2048 := extendCertifiedSegment 15360 1536 512 h1536 checkBlocks_16896_17407
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
