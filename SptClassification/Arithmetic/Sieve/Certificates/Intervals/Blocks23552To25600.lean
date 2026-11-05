/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 23552 through 25599 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_23552_23615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23552_23615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23552_23615 :
    ∀ i : Fin 64, indexedBlockCheck (23552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23552 0 32 h0 checkBlocks_23552_23615_part0
  have h64 := extendCertifiedSegment 23552 32 32 h32 checkBlocks_23552_23615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23616_23679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23616_23679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23616_23679 :
    ∀ i : Fin 64, indexedBlockCheck (23616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23616 0 32 h0 checkBlocks_23616_23679_part0
  have h64 := extendCertifiedSegment 23616 32 32 h32 checkBlocks_23616_23679_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23680_23743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23680_23743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23680_23743 :
    ∀ i : Fin 64, indexedBlockCheck (23680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23680 0 32 h0 checkBlocks_23680_23743_part0
  have h64 := extendCertifiedSegment 23680 32 32 h32 checkBlocks_23680_23743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23744_23807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23744_23807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23744_23807 :
    ∀ i : Fin 64, indexedBlockCheck (23744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23744 0 32 h0 checkBlocks_23744_23807_part0
  have h64 := extendCertifiedSegment 23744 32 32 h32 checkBlocks_23744_23807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23808_23871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23808_23871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23808_23871 :
    ∀ i : Fin 64, indexedBlockCheck (23808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23808 0 32 h0 checkBlocks_23808_23871_part0
  have h64 := extendCertifiedSegment 23808 32 32 h32 checkBlocks_23808_23871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23872_23935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23872_23935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23872_23935 :
    ∀ i : Fin 64, indexedBlockCheck (23872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23872 0 32 h0 checkBlocks_23872_23935_part0
  have h64 := extendCertifiedSegment 23872 32 32 h32 checkBlocks_23872_23935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23936_23999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23936_23999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23936_23999 :
    ∀ i : Fin 64, indexedBlockCheck (23936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23936 0 32 h0 checkBlocks_23936_23999_part0
  have h64 := extendCertifiedSegment 23936 32 32 h32 checkBlocks_23936_23999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24000_24063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24000_24063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24000_24063 :
    ∀ i : Fin 64, indexedBlockCheck (24000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24000 0 32 h0 checkBlocks_24000_24063_part0
  have h64 := extendCertifiedSegment 24000 32 32 h32 checkBlocks_24000_24063_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23552_24063 :
    ∀ i : Fin 512, indexedBlockCheck (23552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23552 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 23552 0 64 h0 checkBlocks_23552_23615
  have h128 := extendCertifiedSegment 23552 64 64 h64 checkBlocks_23616_23679
  have h192 := extendCertifiedSegment 23552 128 64 h128 checkBlocks_23680_23743
  have h256 := extendCertifiedSegment 23552 192 64 h192 checkBlocks_23744_23807
  have h320 := extendCertifiedSegment 23552 256 64 h256 checkBlocks_23808_23871
  have h384 := extendCertifiedSegment 23552 320 64 h320 checkBlocks_23872_23935
  have h448 := extendCertifiedSegment 23552 384 64 h384 checkBlocks_23936_23999
  have h512 := extendCertifiedSegment 23552 448 64 h448 checkBlocks_24000_24063
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_24064_24127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24064_24127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24064_24127 :
    ∀ i : Fin 64, indexedBlockCheck (24064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24064 0 32 h0 checkBlocks_24064_24127_part0
  have h64 := extendCertifiedSegment 24064 32 32 h32 checkBlocks_24064_24127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24128_24191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24128_24191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24128_24191 :
    ∀ i : Fin 64, indexedBlockCheck (24128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24128 0 32 h0 checkBlocks_24128_24191_part0
  have h64 := extendCertifiedSegment 24128 32 32 h32 checkBlocks_24128_24191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24192_24255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24192_24255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24192_24255 :
    ∀ i : Fin 64, indexedBlockCheck (24192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24192 0 32 h0 checkBlocks_24192_24255_part0
  have h64 := extendCertifiedSegment 24192 32 32 h32 checkBlocks_24192_24255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24256_24319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24256_24319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24256_24319 :
    ∀ i : Fin 64, indexedBlockCheck (24256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24256 0 32 h0 checkBlocks_24256_24319_part0
  have h64 := extendCertifiedSegment 24256 32 32 h32 checkBlocks_24256_24319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24320_24383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24320_24383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24320_24383 :
    ∀ i : Fin 64, indexedBlockCheck (24320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24320 0 32 h0 checkBlocks_24320_24383_part0
  have h64 := extendCertifiedSegment 24320 32 32 h32 checkBlocks_24320_24383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24384_24447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24384_24447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24384_24447 :
    ∀ i : Fin 64, indexedBlockCheck (24384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24384 0 32 h0 checkBlocks_24384_24447_part0
  have h64 := extendCertifiedSegment 24384 32 32 h32 checkBlocks_24384_24447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24448_24511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24448_24511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24448_24511 :
    ∀ i : Fin 64, indexedBlockCheck (24448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24448 0 32 h0 checkBlocks_24448_24511_part0
  have h64 := extendCertifiedSegment 24448 32 32 h32 checkBlocks_24448_24511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24512_24575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24512_24575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24512_24575 :
    ∀ i : Fin 64, indexedBlockCheck (24512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24512 0 32 h0 checkBlocks_24512_24575_part0
  have h64 := extendCertifiedSegment 24512 32 32 h32 checkBlocks_24512_24575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24064_24575 :
    ∀ i : Fin 512, indexedBlockCheck (24064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24064 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 24064 0 64 h0 checkBlocks_24064_24127
  have h128 := extendCertifiedSegment 24064 64 64 h64 checkBlocks_24128_24191
  have h192 := extendCertifiedSegment 24064 128 64 h128 checkBlocks_24192_24255
  have h256 := extendCertifiedSegment 24064 192 64 h192 checkBlocks_24256_24319
  have h320 := extendCertifiedSegment 24064 256 64 h256 checkBlocks_24320_24383
  have h384 := extendCertifiedSegment 24064 320 64 h320 checkBlocks_24384_24447
  have h448 := extendCertifiedSegment 24064 384 64 h384 checkBlocks_24448_24511
  have h512 := extendCertifiedSegment 24064 448 64 h448 checkBlocks_24512_24575
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_24576_24639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24576_24639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24576_24639 :
    ∀ i : Fin 64, indexedBlockCheck (24576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24576 0 32 h0 checkBlocks_24576_24639_part0
  have h64 := extendCertifiedSegment 24576 32 32 h32 checkBlocks_24576_24639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24640_24703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24640_24703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24640_24703 :
    ∀ i : Fin 64, indexedBlockCheck (24640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24640 0 32 h0 checkBlocks_24640_24703_part0
  have h64 := extendCertifiedSegment 24640 32 32 h32 checkBlocks_24640_24703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24704_24767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24704_24767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24704_24767 :
    ∀ i : Fin 64, indexedBlockCheck (24704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24704 0 32 h0 checkBlocks_24704_24767_part0
  have h64 := extendCertifiedSegment 24704 32 32 h32 checkBlocks_24704_24767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24768_24831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24768_24831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24768_24831 :
    ∀ i : Fin 64, indexedBlockCheck (24768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24768 0 32 h0 checkBlocks_24768_24831_part0
  have h64 := extendCertifiedSegment 24768 32 32 h32 checkBlocks_24768_24831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24832_24895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24832_24895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24832_24895 :
    ∀ i : Fin 64, indexedBlockCheck (24832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24832 0 32 h0 checkBlocks_24832_24895_part0
  have h64 := extendCertifiedSegment 24832 32 32 h32 checkBlocks_24832_24895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24896_24959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24896_24959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24896_24959 :
    ∀ i : Fin 64, indexedBlockCheck (24896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24896 0 32 h0 checkBlocks_24896_24959_part0
  have h64 := extendCertifiedSegment 24896 32 32 h32 checkBlocks_24896_24959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24960_25023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (24960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24960_25023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (24992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_24960_25023 :
    ∀ i : Fin 64, indexedBlockCheck (24960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 24960 0 32 h0 checkBlocks_24960_25023_part0
  have h64 := extendCertifiedSegment 24960 32 32 h32 checkBlocks_24960_25023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25024_25087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25024_25087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25024_25087 :
    ∀ i : Fin 64, indexedBlockCheck (25024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25024 0 32 h0 checkBlocks_25024_25087_part0
  have h64 := extendCertifiedSegment 25024 32 32 h32 checkBlocks_25024_25087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_24576_25087 :
    ∀ i : Fin 512, indexedBlockCheck (24576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (24576 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 24576 0 64 h0 checkBlocks_24576_24639
  have h128 := extendCertifiedSegment 24576 64 64 h64 checkBlocks_24640_24703
  have h192 := extendCertifiedSegment 24576 128 64 h128 checkBlocks_24704_24767
  have h256 := extendCertifiedSegment 24576 192 64 h192 checkBlocks_24768_24831
  have h320 := extendCertifiedSegment 24576 256 64 h256 checkBlocks_24832_24895
  have h384 := extendCertifiedSegment 24576 320 64 h320 checkBlocks_24896_24959
  have h448 := extendCertifiedSegment 24576 384 64 h384 checkBlocks_24960_25023
  have h512 := extendCertifiedSegment 24576 448 64 h448 checkBlocks_25024_25087
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_25088_25151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25088_25151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25088_25151 :
    ∀ i : Fin 64, indexedBlockCheck (25088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25088 0 32 h0 checkBlocks_25088_25151_part0
  have h64 := extendCertifiedSegment 25088 32 32 h32 checkBlocks_25088_25151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25152_25215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25152_25215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25152_25215 :
    ∀ i : Fin 64, indexedBlockCheck (25152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25152 0 32 h0 checkBlocks_25152_25215_part0
  have h64 := extendCertifiedSegment 25152 32 32 h32 checkBlocks_25152_25215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25216_25279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25216_25279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25216_25279 :
    ∀ i : Fin 64, indexedBlockCheck (25216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25216 0 32 h0 checkBlocks_25216_25279_part0
  have h64 := extendCertifiedSegment 25216 32 32 h32 checkBlocks_25216_25279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25280_25343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25280_25343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25280_25343 :
    ∀ i : Fin 64, indexedBlockCheck (25280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25280 0 32 h0 checkBlocks_25280_25343_part0
  have h64 := extendCertifiedSegment 25280 32 32 h32 checkBlocks_25280_25343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25344_25407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25344_25407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25344_25407 :
    ∀ i : Fin 64, indexedBlockCheck (25344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25344 0 32 h0 checkBlocks_25344_25407_part0
  have h64 := extendCertifiedSegment 25344 32 32 h32 checkBlocks_25344_25407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25408_25471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25408_25471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25408_25471 :
    ∀ i : Fin 64, indexedBlockCheck (25408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25408 0 32 h0 checkBlocks_25408_25471_part0
  have h64 := extendCertifiedSegment 25408 32 32 h32 checkBlocks_25408_25471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25472_25535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25472_25535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25472_25535 :
    ∀ i : Fin 64, indexedBlockCheck (25472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25472 0 32 h0 checkBlocks_25472_25535_part0
  have h64 := extendCertifiedSegment 25472 32 32 h32 checkBlocks_25472_25535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25536_25599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (25536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25536_25599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (25568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25536_25599 :
    ∀ i : Fin 64, indexedBlockCheck (25536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 25536 0 32 h0 checkBlocks_25536_25599_part0
  have h64 := extendCertifiedSegment 25536 32 32 h32 checkBlocks_25536_25599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_25088_25599 :
    ∀ i : Fin 512, indexedBlockCheck (25088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25088 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 25088 0 64 h0 checkBlocks_25088_25151
  have h128 := extendCertifiedSegment 25088 64 64 h64 checkBlocks_25152_25215
  have h192 := extendCertifiedSegment 25088 128 64 h128 checkBlocks_25216_25279
  have h256 := extendCertifiedSegment 25088 192 64 h192 checkBlocks_25280_25343
  have h320 := extendCertifiedSegment 25088 256 64 h256 checkBlocks_25344_25407
  have h384 := extendCertifiedSegment 25088 320 64 h320 checkBlocks_25408_25471
  have h448 := extendCertifiedSegment 25088 384 64 h384 checkBlocks_25472_25535
  have h512 := extendCertifiedSegment 25088 448 64 h448 checkBlocks_25536_25599
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [23552, 25600) passes the packed checker. -/
public theorem blocks_in_23552_25600 :
    ∀ i : Fin 2048, indexedBlockCheck (23552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23552 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 23552 0 512 h0 checkBlocks_23552_24063
  have h1024 := extendCertifiedSegment 23552 512 512 h512 checkBlocks_24064_24575
  have h1536 := extendCertifiedSegment 23552 1024 512 h1024 checkBlocks_24576_25087
  have h2048 := extendCertifiedSegment 23552 1536 512 h1536 checkBlocks_25088_25599
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
