/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 70656 through 72703 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_70656_70719_part0 :
    ∀ i : Fin 32, indexedBlockCheck (70656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70656_70719_part1 :
    ∀ i : Fin 32, indexedBlockCheck (70688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70656_70719 :
    ∀ i : Fin 64, indexedBlockCheck (70656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70656 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 70656 0 32 h0 checkBlocks_70656_70719_part0
  have h64 := extendCertifiedSegment 70656 32 32 h32 checkBlocks_70656_70719_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_70720_70783_part0 :
    ∀ i : Fin 32, indexedBlockCheck (70720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70720_70783_part1 :
    ∀ i : Fin 32, indexedBlockCheck (70752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70720_70783 :
    ∀ i : Fin 64, indexedBlockCheck (70720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70720 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 70720 0 32 h0 checkBlocks_70720_70783_part0
  have h64 := extendCertifiedSegment 70720 32 32 h32 checkBlocks_70720_70783_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_70784_70847_part0 :
    ∀ i : Fin 32, indexedBlockCheck (70784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70784_70847_part1 :
    ∀ i : Fin 32, indexedBlockCheck (70816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70784_70847 :
    ∀ i : Fin 64, indexedBlockCheck (70784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70784 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 70784 0 32 h0 checkBlocks_70784_70847_part0
  have h64 := extendCertifiedSegment 70784 32 32 h32 checkBlocks_70784_70847_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_70848_70911_part0 :
    ∀ i : Fin 32, indexedBlockCheck (70848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70848_70911_part1 :
    ∀ i : Fin 32, indexedBlockCheck (70880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70848_70911 :
    ∀ i : Fin 64, indexedBlockCheck (70848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70848 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 70848 0 32 h0 checkBlocks_70848_70911_part0
  have h64 := extendCertifiedSegment 70848 32 32 h32 checkBlocks_70848_70911_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_70912_70975_part0 :
    ∀ i : Fin 32, indexedBlockCheck (70912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70912_70975_part1 :
    ∀ i : Fin 32, indexedBlockCheck (70944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70912_70975 :
    ∀ i : Fin 64, indexedBlockCheck (70912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70912 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 70912 0 32 h0 checkBlocks_70912_70975_part0
  have h64 := extendCertifiedSegment 70912 32 32 h32 checkBlocks_70912_70975_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_70976_71039_part0 :
    ∀ i : Fin 32, indexedBlockCheck (70976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70976_71039_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70976_71039 :
    ∀ i : Fin 64, indexedBlockCheck (70976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70976 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 70976 0 32 h0 checkBlocks_70976_71039_part0
  have h64 := extendCertifiedSegment 70976 32 32 h32 checkBlocks_70976_71039_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71040_71103_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71040_71103_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71040_71103 :
    ∀ i : Fin 64, indexedBlockCheck (71040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71040 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71040 0 32 h0 checkBlocks_71040_71103_part0
  have h64 := extendCertifiedSegment 71040 32 32 h32 checkBlocks_71040_71103_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71104_71167_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71104_71167_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71104_71167 :
    ∀ i : Fin 64, indexedBlockCheck (71104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71104 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71104 0 32 h0 checkBlocks_71104_71167_part0
  have h64 := extendCertifiedSegment 71104 32 32 h32 checkBlocks_71104_71167_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_70656_71167 :
    ∀ i : Fin 512, indexedBlockCheck (70656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70656 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 70656 0 64 h0 checkBlocks_70656_70719
  have h128 := extendCertifiedSegment 70656 64 64 h64 checkBlocks_70720_70783
  have h192 := extendCertifiedSegment 70656 128 64 h128 checkBlocks_70784_70847
  have h256 := extendCertifiedSegment 70656 192 64 h192 checkBlocks_70848_70911
  have h320 := extendCertifiedSegment 70656 256 64 h256 checkBlocks_70912_70975
  have h384 := extendCertifiedSegment 70656 320 64 h320 checkBlocks_70976_71039
  have h448 := extendCertifiedSegment 70656 384 64 h384 checkBlocks_71040_71103
  have h512 := extendCertifiedSegment 70656 448 64 h448 checkBlocks_71104_71167
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_71168_71231_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71168_71231_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71168_71231 :
    ∀ i : Fin 64, indexedBlockCheck (71168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71168 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71168 0 32 h0 checkBlocks_71168_71231_part0
  have h64 := extendCertifiedSegment 71168 32 32 h32 checkBlocks_71168_71231_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71232_71295_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71232_71295_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71232_71295 :
    ∀ i : Fin 64, indexedBlockCheck (71232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71232 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71232 0 32 h0 checkBlocks_71232_71295_part0
  have h64 := extendCertifiedSegment 71232 32 32 h32 checkBlocks_71232_71295_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71296_71359_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71296_71359_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71296_71359 :
    ∀ i : Fin 64, indexedBlockCheck (71296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71296 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71296 0 32 h0 checkBlocks_71296_71359_part0
  have h64 := extendCertifiedSegment 71296 32 32 h32 checkBlocks_71296_71359_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71360_71423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71360_71423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71360_71423 :
    ∀ i : Fin 64, indexedBlockCheck (71360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71360 0 32 h0 checkBlocks_71360_71423_part0
  have h64 := extendCertifiedSegment 71360 32 32 h32 checkBlocks_71360_71423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71424_71487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71424_71487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71424_71487 :
    ∀ i : Fin 64, indexedBlockCheck (71424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71424 0 32 h0 checkBlocks_71424_71487_part0
  have h64 := extendCertifiedSegment 71424 32 32 h32 checkBlocks_71424_71487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71488_71551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71488_71551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71488_71551 :
    ∀ i : Fin 64, indexedBlockCheck (71488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71488 0 32 h0 checkBlocks_71488_71551_part0
  have h64 := extendCertifiedSegment 71488 32 32 h32 checkBlocks_71488_71551_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71552_71615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71552_71615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71552_71615 :
    ∀ i : Fin 64, indexedBlockCheck (71552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71552 0 32 h0 checkBlocks_71552_71615_part0
  have h64 := extendCertifiedSegment 71552 32 32 h32 checkBlocks_71552_71615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71616_71679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71616_71679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71616_71679 :
    ∀ i : Fin 64, indexedBlockCheck (71616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71616 0 32 h0 checkBlocks_71616_71679_part0
  have h64 := extendCertifiedSegment 71616 32 32 h32 checkBlocks_71616_71679_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71168_71679 :
    ∀ i : Fin 512, indexedBlockCheck (71168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71168 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 71168 0 64 h0 checkBlocks_71168_71231
  have h128 := extendCertifiedSegment 71168 64 64 h64 checkBlocks_71232_71295
  have h192 := extendCertifiedSegment 71168 128 64 h128 checkBlocks_71296_71359
  have h256 := extendCertifiedSegment 71168 192 64 h192 checkBlocks_71360_71423
  have h320 := extendCertifiedSegment 71168 256 64 h256 checkBlocks_71424_71487
  have h384 := extendCertifiedSegment 71168 320 64 h320 checkBlocks_71488_71551
  have h448 := extendCertifiedSegment 71168 384 64 h384 checkBlocks_71552_71615
  have h512 := extendCertifiedSegment 71168 448 64 h448 checkBlocks_71616_71679
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_71680_71743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71680_71743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71680_71743 :
    ∀ i : Fin 64, indexedBlockCheck (71680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71680 0 32 h0 checkBlocks_71680_71743_part0
  have h64 := extendCertifiedSegment 71680 32 32 h32 checkBlocks_71680_71743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71744_71807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71744_71807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71744_71807 :
    ∀ i : Fin 64, indexedBlockCheck (71744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71744 0 32 h0 checkBlocks_71744_71807_part0
  have h64 := extendCertifiedSegment 71744 32 32 h32 checkBlocks_71744_71807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71808_71871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71808_71871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71808_71871 :
    ∀ i : Fin 64, indexedBlockCheck (71808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71808 0 32 h0 checkBlocks_71808_71871_part0
  have h64 := extendCertifiedSegment 71808 32 32 h32 checkBlocks_71808_71871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71872_71935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71872_71935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71872_71935 :
    ∀ i : Fin 64, indexedBlockCheck (71872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71872 0 32 h0 checkBlocks_71872_71935_part0
  have h64 := extendCertifiedSegment 71872 32 32 h32 checkBlocks_71872_71935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71936_71999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (71936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71936_71999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (71968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71936_71999 :
    ∀ i : Fin 64, indexedBlockCheck (71936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 71936 0 32 h0 checkBlocks_71936_71999_part0
  have h64 := extendCertifiedSegment 71936 32 32 h32 checkBlocks_71936_71999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72000_72063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72000_72063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72000_72063 :
    ∀ i : Fin 64, indexedBlockCheck (72000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72000 0 32 h0 checkBlocks_72000_72063_part0
  have h64 := extendCertifiedSegment 72000 32 32 h32 checkBlocks_72000_72063_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72064_72127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72064_72127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72064_72127 :
    ∀ i : Fin 64, indexedBlockCheck (72064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72064 0 32 h0 checkBlocks_72064_72127_part0
  have h64 := extendCertifiedSegment 72064 32 32 h32 checkBlocks_72064_72127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72128_72191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72128_72191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72128_72191 :
    ∀ i : Fin 64, indexedBlockCheck (72128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72128 0 32 h0 checkBlocks_72128_72191_part0
  have h64 := extendCertifiedSegment 72128 32 32 h32 checkBlocks_72128_72191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_71680_72191 :
    ∀ i : Fin 512, indexedBlockCheck (71680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71680 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 71680 0 64 h0 checkBlocks_71680_71743
  have h128 := extendCertifiedSegment 71680 64 64 h64 checkBlocks_71744_71807
  have h192 := extendCertifiedSegment 71680 128 64 h128 checkBlocks_71808_71871
  have h256 := extendCertifiedSegment 71680 192 64 h192 checkBlocks_71872_71935
  have h320 := extendCertifiedSegment 71680 256 64 h256 checkBlocks_71936_71999
  have h384 := extendCertifiedSegment 71680 320 64 h320 checkBlocks_72000_72063
  have h448 := extendCertifiedSegment 71680 384 64 h384 checkBlocks_72064_72127
  have h512 := extendCertifiedSegment 71680 448 64 h448 checkBlocks_72128_72191
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_72192_72255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72192_72255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72192_72255 :
    ∀ i : Fin 64, indexedBlockCheck (72192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72192 0 32 h0 checkBlocks_72192_72255_part0
  have h64 := extendCertifiedSegment 72192 32 32 h32 checkBlocks_72192_72255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72256_72319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72256_72319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72256_72319 :
    ∀ i : Fin 64, indexedBlockCheck (72256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72256 0 32 h0 checkBlocks_72256_72319_part0
  have h64 := extendCertifiedSegment 72256 32 32 h32 checkBlocks_72256_72319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72320_72383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72320_72383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72320_72383 :
    ∀ i : Fin 64, indexedBlockCheck (72320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72320 0 32 h0 checkBlocks_72320_72383_part0
  have h64 := extendCertifiedSegment 72320 32 32 h32 checkBlocks_72320_72383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72384_72447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72384_72447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72384_72447 :
    ∀ i : Fin 64, indexedBlockCheck (72384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72384 0 32 h0 checkBlocks_72384_72447_part0
  have h64 := extendCertifiedSegment 72384 32 32 h32 checkBlocks_72384_72447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72448_72511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72448_72511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72448_72511 :
    ∀ i : Fin 64, indexedBlockCheck (72448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72448 0 32 h0 checkBlocks_72448_72511_part0
  have h64 := extendCertifiedSegment 72448 32 32 h32 checkBlocks_72448_72511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72512_72575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72512_72575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72512_72575 :
    ∀ i : Fin 64, indexedBlockCheck (72512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72512 0 32 h0 checkBlocks_72512_72575_part0
  have h64 := extendCertifiedSegment 72512 32 32 h32 checkBlocks_72512_72575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72576_72639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72576_72639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72576_72639 :
    ∀ i : Fin 64, indexedBlockCheck (72576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72576 0 32 h0 checkBlocks_72576_72639_part0
  have h64 := extendCertifiedSegment 72576 32 32 h32 checkBlocks_72576_72639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72640_72703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72640_72703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72640_72703 :
    ∀ i : Fin 64, indexedBlockCheck (72640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72640 0 32 h0 checkBlocks_72640_72703_part0
  have h64 := extendCertifiedSegment 72640 32 32 h32 checkBlocks_72640_72703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72192_72703 :
    ∀ i : Fin 512, indexedBlockCheck (72192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72192 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 72192 0 64 h0 checkBlocks_72192_72255
  have h128 := extendCertifiedSegment 72192 64 64 h64 checkBlocks_72256_72319
  have h192 := extendCertifiedSegment 72192 128 64 h128 checkBlocks_72320_72383
  have h256 := extendCertifiedSegment 72192 192 64 h192 checkBlocks_72384_72447
  have h320 := extendCertifiedSegment 72192 256 64 h256 checkBlocks_72448_72511
  have h384 := extendCertifiedSegment 72192 320 64 h320 checkBlocks_72512_72575
  have h448 := extendCertifiedSegment 72192 384 64 h384 checkBlocks_72576_72639
  have h512 := extendCertifiedSegment 72192 448 64 h448 checkBlocks_72640_72703
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [70656, 72704) passes the packed checker. -/
public theorem blocks_in_70656_72704 :
    ∀ i : Fin 2048, indexedBlockCheck (70656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70656 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 70656 0 512 h0 checkBlocks_70656_71167
  have h1024 := extendCertifiedSegment 70656 512 512 h512 checkBlocks_71168_71679
  have h1536 := extendCertifiedSegment 70656 1024 512 h1024 checkBlocks_71680_72191
  have h2048 := extendCertifiedSegment 70656 1536 512 h1536 checkBlocks_72192_72703
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
