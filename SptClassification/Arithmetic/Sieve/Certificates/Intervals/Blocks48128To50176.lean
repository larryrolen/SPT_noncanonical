/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 48128 through 50175 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_48128_48191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48128_48191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48128_48191 :
    ∀ i : Fin 64, indexedBlockCheck (48128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48128 0 32 h0 checkBlocks_48128_48191_part0
  have h64 := extendCertifiedSegment 48128 32 32 h32 checkBlocks_48128_48191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48192_48255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48192_48255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48192_48255 :
    ∀ i : Fin 64, indexedBlockCheck (48192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48192 0 32 h0 checkBlocks_48192_48255_part0
  have h64 := extendCertifiedSegment 48192 32 32 h32 checkBlocks_48192_48255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48256_48319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48256_48319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48256_48319 :
    ∀ i : Fin 64, indexedBlockCheck (48256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48256 0 32 h0 checkBlocks_48256_48319_part0
  have h64 := extendCertifiedSegment 48256 32 32 h32 checkBlocks_48256_48319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48320_48383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48320_48383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48320_48383 :
    ∀ i : Fin 64, indexedBlockCheck (48320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48320 0 32 h0 checkBlocks_48320_48383_part0
  have h64 := extendCertifiedSegment 48320 32 32 h32 checkBlocks_48320_48383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48384_48447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48384_48447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48384_48447 :
    ∀ i : Fin 64, indexedBlockCheck (48384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48384 0 32 h0 checkBlocks_48384_48447_part0
  have h64 := extendCertifiedSegment 48384 32 32 h32 checkBlocks_48384_48447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48448_48511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48448_48511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48448_48511 :
    ∀ i : Fin 64, indexedBlockCheck (48448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48448 0 32 h0 checkBlocks_48448_48511_part0
  have h64 := extendCertifiedSegment 48448 32 32 h32 checkBlocks_48448_48511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48512_48575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48512_48575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48512_48575 :
    ∀ i : Fin 64, indexedBlockCheck (48512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48512 0 32 h0 checkBlocks_48512_48575_part0
  have h64 := extendCertifiedSegment 48512 32 32 h32 checkBlocks_48512_48575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48576_48639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48576_48639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48576_48639 :
    ∀ i : Fin 64, indexedBlockCheck (48576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48576 0 32 h0 checkBlocks_48576_48639_part0
  have h64 := extendCertifiedSegment 48576 32 32 h32 checkBlocks_48576_48639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48128_48639 :
    ∀ i : Fin 512, indexedBlockCheck (48128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48128 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 48128 0 64 h0 checkBlocks_48128_48191
  have h128 := extendCertifiedSegment 48128 64 64 h64 checkBlocks_48192_48255
  have h192 := extendCertifiedSegment 48128 128 64 h128 checkBlocks_48256_48319
  have h256 := extendCertifiedSegment 48128 192 64 h192 checkBlocks_48320_48383
  have h320 := extendCertifiedSegment 48128 256 64 h256 checkBlocks_48384_48447
  have h384 := extendCertifiedSegment 48128 320 64 h320 checkBlocks_48448_48511
  have h448 := extendCertifiedSegment 48128 384 64 h384 checkBlocks_48512_48575
  have h512 := extendCertifiedSegment 48128 448 64 h448 checkBlocks_48576_48639
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_48640_48703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48640_48703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48640_48703 :
    ∀ i : Fin 64, indexedBlockCheck (48640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48640 0 32 h0 checkBlocks_48640_48703_part0
  have h64 := extendCertifiedSegment 48640 32 32 h32 checkBlocks_48640_48703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48704_48767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48704_48767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48704_48767 :
    ∀ i : Fin 64, indexedBlockCheck (48704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48704 0 32 h0 checkBlocks_48704_48767_part0
  have h64 := extendCertifiedSegment 48704 32 32 h32 checkBlocks_48704_48767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48768_48831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48768_48831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48768_48831 :
    ∀ i : Fin 64, indexedBlockCheck (48768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48768 0 32 h0 checkBlocks_48768_48831_part0
  have h64 := extendCertifiedSegment 48768 32 32 h32 checkBlocks_48768_48831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48832_48895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48832_48895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48832_48895 :
    ∀ i : Fin 64, indexedBlockCheck (48832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48832 0 32 h0 checkBlocks_48832_48895_part0
  have h64 := extendCertifiedSegment 48832 32 32 h32 checkBlocks_48832_48895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48896_48959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48896_48959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48896_48959 :
    ∀ i : Fin 64, indexedBlockCheck (48896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48896 0 32 h0 checkBlocks_48896_48959_part0
  have h64 := extendCertifiedSegment 48896 32 32 h32 checkBlocks_48896_48959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48960_49023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48960_49023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48960_49023 :
    ∀ i : Fin 64, indexedBlockCheck (48960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48960 0 32 h0 checkBlocks_48960_49023_part0
  have h64 := extendCertifiedSegment 48960 32 32 h32 checkBlocks_48960_49023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49024_49087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49024_49087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49024_49087 :
    ∀ i : Fin 64, indexedBlockCheck (49024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49024 0 32 h0 checkBlocks_49024_49087_part0
  have h64 := extendCertifiedSegment 49024 32 32 h32 checkBlocks_49024_49087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49088_49151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49088_49151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49088_49151 :
    ∀ i : Fin 64, indexedBlockCheck (49088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49088 0 32 h0 checkBlocks_49088_49151_part0
  have h64 := extendCertifiedSegment 49088 32 32 h32 checkBlocks_49088_49151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48640_49151 :
    ∀ i : Fin 512, indexedBlockCheck (48640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48640 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 48640 0 64 h0 checkBlocks_48640_48703
  have h128 := extendCertifiedSegment 48640 64 64 h64 checkBlocks_48704_48767
  have h192 := extendCertifiedSegment 48640 128 64 h128 checkBlocks_48768_48831
  have h256 := extendCertifiedSegment 48640 192 64 h192 checkBlocks_48832_48895
  have h320 := extendCertifiedSegment 48640 256 64 h256 checkBlocks_48896_48959
  have h384 := extendCertifiedSegment 48640 320 64 h320 checkBlocks_48960_49023
  have h448 := extendCertifiedSegment 48640 384 64 h384 checkBlocks_49024_49087
  have h512 := extendCertifiedSegment 48640 448 64 h448 checkBlocks_49088_49151
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_49152_49215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49152_49215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49152_49215 :
    ∀ i : Fin 64, indexedBlockCheck (49152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49152 0 32 h0 checkBlocks_49152_49215_part0
  have h64 := extendCertifiedSegment 49152 32 32 h32 checkBlocks_49152_49215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49216_49279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49216_49279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49216_49279 :
    ∀ i : Fin 64, indexedBlockCheck (49216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49216 0 32 h0 checkBlocks_49216_49279_part0
  have h64 := extendCertifiedSegment 49216 32 32 h32 checkBlocks_49216_49279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49280_49343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49280_49343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49280_49343 :
    ∀ i : Fin 64, indexedBlockCheck (49280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49280 0 32 h0 checkBlocks_49280_49343_part0
  have h64 := extendCertifiedSegment 49280 32 32 h32 checkBlocks_49280_49343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49344_49407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49344_49407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49344_49407 :
    ∀ i : Fin 64, indexedBlockCheck (49344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49344 0 32 h0 checkBlocks_49344_49407_part0
  have h64 := extendCertifiedSegment 49344 32 32 h32 checkBlocks_49344_49407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49408_49471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49408_49471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49408_49471 :
    ∀ i : Fin 64, indexedBlockCheck (49408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49408 0 32 h0 checkBlocks_49408_49471_part0
  have h64 := extendCertifiedSegment 49408 32 32 h32 checkBlocks_49408_49471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49472_49535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49472_49535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49472_49535 :
    ∀ i : Fin 64, indexedBlockCheck (49472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49472 0 32 h0 checkBlocks_49472_49535_part0
  have h64 := extendCertifiedSegment 49472 32 32 h32 checkBlocks_49472_49535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49536_49599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49536_49599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49536_49599 :
    ∀ i : Fin 64, indexedBlockCheck (49536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49536 0 32 h0 checkBlocks_49536_49599_part0
  have h64 := extendCertifiedSegment 49536 32 32 h32 checkBlocks_49536_49599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49600_49663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49600_49663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49600_49663 :
    ∀ i : Fin 64, indexedBlockCheck (49600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49600 0 32 h0 checkBlocks_49600_49663_part0
  have h64 := extendCertifiedSegment 49600 32 32 h32 checkBlocks_49600_49663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49152_49663 :
    ∀ i : Fin 512, indexedBlockCheck (49152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49152 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 49152 0 64 h0 checkBlocks_49152_49215
  have h128 := extendCertifiedSegment 49152 64 64 h64 checkBlocks_49216_49279
  have h192 := extendCertifiedSegment 49152 128 64 h128 checkBlocks_49280_49343
  have h256 := extendCertifiedSegment 49152 192 64 h192 checkBlocks_49344_49407
  have h320 := extendCertifiedSegment 49152 256 64 h256 checkBlocks_49408_49471
  have h384 := extendCertifiedSegment 49152 320 64 h320 checkBlocks_49472_49535
  have h448 := extendCertifiedSegment 49152 384 64 h384 checkBlocks_49536_49599
  have h512 := extendCertifiedSegment 49152 448 64 h448 checkBlocks_49600_49663
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_49664_49727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49664_49727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49664_49727 :
    ∀ i : Fin 64, indexedBlockCheck (49664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49664 0 32 h0 checkBlocks_49664_49727_part0
  have h64 := extendCertifiedSegment 49664 32 32 h32 checkBlocks_49664_49727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49728_49791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49728_49791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49728_49791 :
    ∀ i : Fin 64, indexedBlockCheck (49728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49728 0 32 h0 checkBlocks_49728_49791_part0
  have h64 := extendCertifiedSegment 49728 32 32 h32 checkBlocks_49728_49791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49792_49855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49792_49855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49792_49855 :
    ∀ i : Fin 64, indexedBlockCheck (49792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49792 0 32 h0 checkBlocks_49792_49855_part0
  have h64 := extendCertifiedSegment 49792 32 32 h32 checkBlocks_49792_49855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49856_49919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49856_49919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49856_49919 :
    ∀ i : Fin 64, indexedBlockCheck (49856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49856 0 32 h0 checkBlocks_49856_49919_part0
  have h64 := extendCertifiedSegment 49856 32 32 h32 checkBlocks_49856_49919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49920_49983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49920_49983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (49952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49920_49983 :
    ∀ i : Fin 64, indexedBlockCheck (49920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49920 0 32 h0 checkBlocks_49920_49983_part0
  have h64 := extendCertifiedSegment 49920 32 32 h32 checkBlocks_49920_49983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49984_50047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (49984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49984_50047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (50016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_49984_50047 :
    ∀ i : Fin 64, indexedBlockCheck (49984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 49984 0 32 h0 checkBlocks_49984_50047_part0
  have h64 := extendCertifiedSegment 49984 32 32 h32 checkBlocks_49984_50047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_50048_50111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (50048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50048_50111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (50080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50048_50111 :
    ∀ i : Fin 64, indexedBlockCheck (50048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (50048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 50048 0 32 h0 checkBlocks_50048_50111_part0
  have h64 := extendCertifiedSegment 50048 32 32 h32 checkBlocks_50048_50111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_50112_50175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (50112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50112_50175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (50144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50112_50175 :
    ∀ i : Fin 64, indexedBlockCheck (50112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (50112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 50112 0 32 h0 checkBlocks_50112_50175_part0
  have h64 := extendCertifiedSegment 50112 32 32 h32 checkBlocks_50112_50175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_49664_50175 :
    ∀ i : Fin 512, indexedBlockCheck (49664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (49664 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 49664 0 64 h0 checkBlocks_49664_49727
  have h128 := extendCertifiedSegment 49664 64 64 h64 checkBlocks_49728_49791
  have h192 := extendCertifiedSegment 49664 128 64 h128 checkBlocks_49792_49855
  have h256 := extendCertifiedSegment 49664 192 64 h192 checkBlocks_49856_49919
  have h320 := extendCertifiedSegment 49664 256 64 h256 checkBlocks_49920_49983
  have h384 := extendCertifiedSegment 49664 320 64 h320 checkBlocks_49984_50047
  have h448 := extendCertifiedSegment 49664 384 64 h384 checkBlocks_50048_50111
  have h512 := extendCertifiedSegment 49664 448 64 h448 checkBlocks_50112_50175
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [48128, 50176) passes the packed checker. -/
public theorem blocks_in_48128_50176 :
    ∀ i : Fin 2048, indexedBlockCheck (48128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48128 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 48128 0 512 h0 checkBlocks_48128_48639
  have h1024 := extendCertifiedSegment 48128 512 512 h512 checkBlocks_48640_49151
  have h1536 := extendCertifiedSegment 48128 1024 512 h1024 checkBlocks_49152_49663
  have h2048 := extendCertifiedSegment 48128 1536 512 h1536 checkBlocks_49664_50175
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
