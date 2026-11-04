/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 0 through 1023 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_0_63_part0 :
    ∀ i : Fin 32, indexedBlockCheck (0 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_0_63_part1 :
    ∀ i : Fin 32, indexedBlockCheck (32 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_0_63 :
    ∀ i : Fin 64, indexedBlockCheck (0 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (0 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 0 0 32 h0 checkBlocks_0_63_part0
  have h64 := extendCertifiedSegment 0 32 32 h32 checkBlocks_0_63_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64_127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64_127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (96 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64_127 :
    ∀ i : Fin 64, indexedBlockCheck (64 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64 0 32 h0 checkBlocks_64_127_part0
  have h64 := extendCertifiedSegment 64 32 32 h32 checkBlocks_64_127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_128_191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_128_191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_128_191 :
    ∀ i : Fin 64, indexedBlockCheck (128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 128 0 32 h0 checkBlocks_128_191_part0
  have h64 := extendCertifiedSegment 128 32 32 h32 checkBlocks_128_191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_192_255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_192_255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_192_255 :
    ∀ i : Fin 64, indexedBlockCheck (192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 192 0 32 h0 checkBlocks_192_255_part0
  have h64 := extendCertifiedSegment 192 32 32 h32 checkBlocks_192_255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_256_319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_256_319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_256_319 :
    ∀ i : Fin 64, indexedBlockCheck (256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 256 0 32 h0 checkBlocks_256_319_part0
  have h64 := extendCertifiedSegment 256 32 32 h32 checkBlocks_256_319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_320_383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_320_383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_320_383 :
    ∀ i : Fin 64, indexedBlockCheck (320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 320 0 32 h0 checkBlocks_320_383_part0
  have h64 := extendCertifiedSegment 320 32 32 h32 checkBlocks_320_383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_384_447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_384_447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_384_447 :
    ∀ i : Fin 64, indexedBlockCheck (384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 384 0 32 h0 checkBlocks_384_447_part0
  have h64 := extendCertifiedSegment 384 32 32 h32 checkBlocks_384_447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_448_511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_448_511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_448_511 :
    ∀ i : Fin 64, indexedBlockCheck (448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 448 0 32 h0 checkBlocks_448_511_part0
  have h64 := extendCertifiedSegment 448 32 32 h32 checkBlocks_448_511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_0_511 :
    ∀ i : Fin 512, indexedBlockCheck (0 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (0 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 0 0 64 h0 checkBlocks_0_63
  have h128 := extendCertifiedSegment 0 64 64 h64 checkBlocks_64_127
  have h192 := extendCertifiedSegment 0 128 64 h128 checkBlocks_128_191
  have h256 := extendCertifiedSegment 0 192 64 h192 checkBlocks_192_255
  have h320 := extendCertifiedSegment 0 256 64 h256 checkBlocks_256_319
  have h384 := extendCertifiedSegment 0 320 64 h320 checkBlocks_320_383
  have h448 := extendCertifiedSegment 0 384 64 h384 checkBlocks_384_447
  have h512 := extendCertifiedSegment 0 448 64 h448 checkBlocks_448_511
  intro i
  exact h512 i.val i.isLt
private theorem checkBlocks_512_575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_512_575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_512_575 :
    ∀ i : Fin 64, indexedBlockCheck (512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 512 0 32 h0 checkBlocks_512_575_part0
  have h64 := extendCertifiedSegment 512 32 32 h32 checkBlocks_512_575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_576_639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_576_639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_576_639 :
    ∀ i : Fin 64, indexedBlockCheck (576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 576 0 32 h0 checkBlocks_576_639_part0
  have h64 := extendCertifiedSegment 576 32 32 h32 checkBlocks_576_639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_640_703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_640_703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_640_703 :
    ∀ i : Fin 64, indexedBlockCheck (640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 640 0 32 h0 checkBlocks_640_703_part0
  have h64 := extendCertifiedSegment 640 32 32 h32 checkBlocks_640_703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_704_767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_704_767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_704_767 :
    ∀ i : Fin 64, indexedBlockCheck (704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 704 0 32 h0 checkBlocks_704_767_part0
  have h64 := extendCertifiedSegment 704 32 32 h32 checkBlocks_704_767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_768_831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_768_831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_768_831 :
    ∀ i : Fin 64, indexedBlockCheck (768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 768 0 32 h0 checkBlocks_768_831_part0
  have h64 := extendCertifiedSegment 768 32 32 h32 checkBlocks_768_831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_832_895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_832_895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_832_895 :
    ∀ i : Fin 64, indexedBlockCheck (832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 832 0 32 h0 checkBlocks_832_895_part0
  have h64 := extendCertifiedSegment 832 32 32 h32 checkBlocks_832_895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_896_959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_896_959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_896_959 :
    ∀ i : Fin 64, indexedBlockCheck (896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 896 0 32 h0 checkBlocks_896_959_part0
  have h64 := extendCertifiedSegment 896 32 32 h32 checkBlocks_896_959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_960_1023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_960_1023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_960_1023 :
    ∀ i : Fin 64, indexedBlockCheck (960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 960 0 32 h0 checkBlocks_960_1023_part0
  have h64 := extendCertifiedSegment 960 32 32 h32 checkBlocks_960_1023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_512_1023 :
    ∀ i : Fin 512, indexedBlockCheck (512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (512 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 512 0 64 h0 checkBlocks_512_575
  have h128 := extendCertifiedSegment 512 64 64 h64 checkBlocks_576_639
  have h192 := extendCertifiedSegment 512 128 64 h128 checkBlocks_640_703
  have h256 := extendCertifiedSegment 512 192 64 h192 checkBlocks_704_767
  have h320 := extendCertifiedSegment 512 256 64 h256 checkBlocks_768_831
  have h384 := extendCertifiedSegment 512 320 64 h320 checkBlocks_832_895
  have h448 := extendCertifiedSegment 512 384 64 h384 checkBlocks_896_959
  have h512 := extendCertifiedSegment 512 448 64 h448 checkBlocks_960_1023
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [0, 1024) passes the packed checker. -/
public theorem blocks_in_0_1024 :
    ∀ i : Fin 1024, indexedBlockCheck (0 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (0 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 0 0 512 h0 checkBlocks_0_511
  have h1024 := extendCertifiedSegment 0 512 512 h512 checkBlocks_512_1023
  intro i
  exact h1024 i.val i.isLt

end SptClassification.Sieve
