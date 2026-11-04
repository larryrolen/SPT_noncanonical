/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 39936 through 41983 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_39936_39999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39936_39999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39936_39999 :
    ∀ i : Fin 64, indexedBlockCheck (39936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39936 0 32 h0 checkBlocks_39936_39999_part0
  have h64 := extendCertifiedSegment 39936 32 32 h32 checkBlocks_39936_39999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40000_40063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40000_40063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40000_40063 :
    ∀ i : Fin 64, indexedBlockCheck (40000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40000 0 32 h0 checkBlocks_40000_40063_part0
  have h64 := extendCertifiedSegment 40000 32 32 h32 checkBlocks_40000_40063_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40064_40127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40064_40127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40064_40127 :
    ∀ i : Fin 64, indexedBlockCheck (40064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40064 0 32 h0 checkBlocks_40064_40127_part0
  have h64 := extendCertifiedSegment 40064 32 32 h32 checkBlocks_40064_40127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40128_40191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40128_40191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40128_40191 :
    ∀ i : Fin 64, indexedBlockCheck (40128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40128 0 32 h0 checkBlocks_40128_40191_part0
  have h64 := extendCertifiedSegment 40128 32 32 h32 checkBlocks_40128_40191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40192_40255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40192_40255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40192_40255 :
    ∀ i : Fin 64, indexedBlockCheck (40192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40192 0 32 h0 checkBlocks_40192_40255_part0
  have h64 := extendCertifiedSegment 40192 32 32 h32 checkBlocks_40192_40255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40256_40319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40256_40319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40256_40319 :
    ∀ i : Fin 64, indexedBlockCheck (40256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40256 0 32 h0 checkBlocks_40256_40319_part0
  have h64 := extendCertifiedSegment 40256 32 32 h32 checkBlocks_40256_40319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40320_40383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40320_40383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40320_40383 :
    ∀ i : Fin 64, indexedBlockCheck (40320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40320 0 32 h0 checkBlocks_40320_40383_part0
  have h64 := extendCertifiedSegment 40320 32 32 h32 checkBlocks_40320_40383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40384_40447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40384_40447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40384_40447 :
    ∀ i : Fin 64, indexedBlockCheck (40384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40384 0 32 h0 checkBlocks_40384_40447_part0
  have h64 := extendCertifiedSegment 40384 32 32 h32 checkBlocks_40384_40447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39936_40447 :
    ∀ i : Fin 512, indexedBlockCheck (39936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39936 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 39936 0 64 h0 checkBlocks_39936_39999
  have h128 := extendCertifiedSegment 39936 64 64 h64 checkBlocks_40000_40063
  have h192 := extendCertifiedSegment 39936 128 64 h128 checkBlocks_40064_40127
  have h256 := extendCertifiedSegment 39936 192 64 h192 checkBlocks_40128_40191
  have h320 := extendCertifiedSegment 39936 256 64 h256 checkBlocks_40192_40255
  have h384 := extendCertifiedSegment 39936 320 64 h320 checkBlocks_40256_40319
  have h448 := extendCertifiedSegment 39936 384 64 h384 checkBlocks_40320_40383
  have h512 := extendCertifiedSegment 39936 448 64 h448 checkBlocks_40384_40447
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_40448_40511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40448_40511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40448_40511 :
    ∀ i : Fin 64, indexedBlockCheck (40448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40448 0 32 h0 checkBlocks_40448_40511_part0
  have h64 := extendCertifiedSegment 40448 32 32 h32 checkBlocks_40448_40511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40512_40575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40512_40575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40512_40575 :
    ∀ i : Fin 64, indexedBlockCheck (40512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40512 0 32 h0 checkBlocks_40512_40575_part0
  have h64 := extendCertifiedSegment 40512 32 32 h32 checkBlocks_40512_40575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40576_40639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40576_40639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40576_40639 :
    ∀ i : Fin 64, indexedBlockCheck (40576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40576 0 32 h0 checkBlocks_40576_40639_part0
  have h64 := extendCertifiedSegment 40576 32 32 h32 checkBlocks_40576_40639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40640_40703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40640_40703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40640_40703 :
    ∀ i : Fin 64, indexedBlockCheck (40640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40640 0 32 h0 checkBlocks_40640_40703_part0
  have h64 := extendCertifiedSegment 40640 32 32 h32 checkBlocks_40640_40703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40704_40767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40704_40767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40704_40767 :
    ∀ i : Fin 64, indexedBlockCheck (40704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40704 0 32 h0 checkBlocks_40704_40767_part0
  have h64 := extendCertifiedSegment 40704 32 32 h32 checkBlocks_40704_40767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40768_40831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40768_40831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40768_40831 :
    ∀ i : Fin 64, indexedBlockCheck (40768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40768 0 32 h0 checkBlocks_40768_40831_part0
  have h64 := extendCertifiedSegment 40768 32 32 h32 checkBlocks_40768_40831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40832_40895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40832_40895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40832_40895 :
    ∀ i : Fin 64, indexedBlockCheck (40832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40832 0 32 h0 checkBlocks_40832_40895_part0
  have h64 := extendCertifiedSegment 40832 32 32 h32 checkBlocks_40832_40895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40896_40959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40896_40959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40896_40959 :
    ∀ i : Fin 64, indexedBlockCheck (40896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40896 0 32 h0 checkBlocks_40896_40959_part0
  have h64 := extendCertifiedSegment 40896 32 32 h32 checkBlocks_40896_40959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40448_40959 :
    ∀ i : Fin 512, indexedBlockCheck (40448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40448 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 40448 0 64 h0 checkBlocks_40448_40511
  have h128 := extendCertifiedSegment 40448 64 64 h64 checkBlocks_40512_40575
  have h192 := extendCertifiedSegment 40448 128 64 h128 checkBlocks_40576_40639
  have h256 := extendCertifiedSegment 40448 192 64 h192 checkBlocks_40640_40703
  have h320 := extendCertifiedSegment 40448 256 64 h256 checkBlocks_40704_40767
  have h384 := extendCertifiedSegment 40448 320 64 h320 checkBlocks_40768_40831
  have h448 := extendCertifiedSegment 40448 384 64 h384 checkBlocks_40832_40895
  have h512 := extendCertifiedSegment 40448 448 64 h448 checkBlocks_40896_40959
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_40960_41023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (40960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40960_41023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (40992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40960_41023 :
    ∀ i : Fin 64, indexedBlockCheck (40960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 40960 0 32 h0 checkBlocks_40960_41023_part0
  have h64 := extendCertifiedSegment 40960 32 32 h32 checkBlocks_40960_41023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41024_41087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41024_41087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41024_41087 :
    ∀ i : Fin 64, indexedBlockCheck (41024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41024 0 32 h0 checkBlocks_41024_41087_part0
  have h64 := extendCertifiedSegment 41024 32 32 h32 checkBlocks_41024_41087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41088_41151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41088_41151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41088_41151 :
    ∀ i : Fin 64, indexedBlockCheck (41088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41088 0 32 h0 checkBlocks_41088_41151_part0
  have h64 := extendCertifiedSegment 41088 32 32 h32 checkBlocks_41088_41151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41152_41215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41152_41215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41152_41215 :
    ∀ i : Fin 64, indexedBlockCheck (41152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41152 0 32 h0 checkBlocks_41152_41215_part0
  have h64 := extendCertifiedSegment 41152 32 32 h32 checkBlocks_41152_41215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41216_41279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41216_41279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41216_41279 :
    ∀ i : Fin 64, indexedBlockCheck (41216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41216 0 32 h0 checkBlocks_41216_41279_part0
  have h64 := extendCertifiedSegment 41216 32 32 h32 checkBlocks_41216_41279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41280_41343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41280_41343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41280_41343 :
    ∀ i : Fin 64, indexedBlockCheck (41280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41280 0 32 h0 checkBlocks_41280_41343_part0
  have h64 := extendCertifiedSegment 41280 32 32 h32 checkBlocks_41280_41343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41344_41407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41344_41407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41344_41407 :
    ∀ i : Fin 64, indexedBlockCheck (41344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41344 0 32 h0 checkBlocks_41344_41407_part0
  have h64 := extendCertifiedSegment 41344 32 32 h32 checkBlocks_41344_41407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41408_41471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41408_41471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41408_41471 :
    ∀ i : Fin 64, indexedBlockCheck (41408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41408 0 32 h0 checkBlocks_41408_41471_part0
  have h64 := extendCertifiedSegment 41408 32 32 h32 checkBlocks_41408_41471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_40960_41471 :
    ∀ i : Fin 512, indexedBlockCheck (40960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40960 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 40960 0 64 h0 checkBlocks_40960_41023
  have h128 := extendCertifiedSegment 40960 64 64 h64 checkBlocks_41024_41087
  have h192 := extendCertifiedSegment 40960 128 64 h128 checkBlocks_41088_41151
  have h256 := extendCertifiedSegment 40960 192 64 h192 checkBlocks_41152_41215
  have h320 := extendCertifiedSegment 40960 256 64 h256 checkBlocks_41216_41279
  have h384 := extendCertifiedSegment 40960 320 64 h320 checkBlocks_41280_41343
  have h448 := extendCertifiedSegment 40960 384 64 h384 checkBlocks_41344_41407
  have h512 := extendCertifiedSegment 40960 448 64 h448 checkBlocks_41408_41471
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_41472_41535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41472_41535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41472_41535 :
    ∀ i : Fin 64, indexedBlockCheck (41472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41472 0 32 h0 checkBlocks_41472_41535_part0
  have h64 := extendCertifiedSegment 41472 32 32 h32 checkBlocks_41472_41535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41536_41599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41536_41599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41536_41599 :
    ∀ i : Fin 64, indexedBlockCheck (41536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41536 0 32 h0 checkBlocks_41536_41599_part0
  have h64 := extendCertifiedSegment 41536 32 32 h32 checkBlocks_41536_41599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41600_41663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41600_41663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41600_41663 :
    ∀ i : Fin 64, indexedBlockCheck (41600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41600 0 32 h0 checkBlocks_41600_41663_part0
  have h64 := extendCertifiedSegment 41600 32 32 h32 checkBlocks_41600_41663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41664_41727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41664_41727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41664_41727 :
    ∀ i : Fin 64, indexedBlockCheck (41664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41664 0 32 h0 checkBlocks_41664_41727_part0
  have h64 := extendCertifiedSegment 41664 32 32 h32 checkBlocks_41664_41727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41728_41791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41728_41791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41728_41791 :
    ∀ i : Fin 64, indexedBlockCheck (41728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41728 0 32 h0 checkBlocks_41728_41791_part0
  have h64 := extendCertifiedSegment 41728 32 32 h32 checkBlocks_41728_41791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41792_41855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41792_41855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41792_41855 :
    ∀ i : Fin 64, indexedBlockCheck (41792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41792 0 32 h0 checkBlocks_41792_41855_part0
  have h64 := extendCertifiedSegment 41792 32 32 h32 checkBlocks_41792_41855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41856_41919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41856_41919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41856_41919 :
    ∀ i : Fin 64, indexedBlockCheck (41856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41856 0 32 h0 checkBlocks_41856_41919_part0
  have h64 := extendCertifiedSegment 41856 32 32 h32 checkBlocks_41856_41919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41920_41983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41920_41983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (41952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41920_41983 :
    ∀ i : Fin 64, indexedBlockCheck (41920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41920 0 32 h0 checkBlocks_41920_41983_part0
  have h64 := extendCertifiedSegment 41920 32 32 h32 checkBlocks_41920_41983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41472_41983 :
    ∀ i : Fin 512, indexedBlockCheck (41472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41472 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 41472 0 64 h0 checkBlocks_41472_41535
  have h128 := extendCertifiedSegment 41472 64 64 h64 checkBlocks_41536_41599
  have h192 := extendCertifiedSegment 41472 128 64 h128 checkBlocks_41600_41663
  have h256 := extendCertifiedSegment 41472 192 64 h192 checkBlocks_41664_41727
  have h320 := extendCertifiedSegment 41472 256 64 h256 checkBlocks_41728_41791
  have h384 := extendCertifiedSegment 41472 320 64 h320 checkBlocks_41792_41855
  have h448 := extendCertifiedSegment 41472 384 64 h384 checkBlocks_41856_41919
  have h512 := extendCertifiedSegment 41472 448 64 h448 checkBlocks_41920_41983
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [39936, 41984) passes the packed checker. -/
public theorem blocks_in_39936_41984 :
    ∀ i : Fin 2048, indexedBlockCheck (39936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39936 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 39936 0 512 h0 checkBlocks_39936_40447
  have h1024 := extendCertifiedSegment 39936 512 512 h512 checkBlocks_40448_40959
  have h1536 := extendCertifiedSegment 39936 1024 512 h1024 checkBlocks_40960_41471
  have h2048 := extendCertifiedSegment 39936 1536 512 h1536 checkBlocks_41472_41983
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
