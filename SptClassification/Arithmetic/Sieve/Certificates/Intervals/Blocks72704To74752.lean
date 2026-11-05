/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 72704 through 74751 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_72704_72767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72704_72767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72704_72767 :
    ∀ i : Fin 64, indexedBlockCheck (72704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72704 0 32 h0 checkBlocks_72704_72767_part0
  have h64 := extendCertifiedSegment 72704 32 32 h32 checkBlocks_72704_72767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72768_72831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72768_72831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72768_72831 :
    ∀ i : Fin 64, indexedBlockCheck (72768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72768 0 32 h0 checkBlocks_72768_72831_part0
  have h64 := extendCertifiedSegment 72768 32 32 h32 checkBlocks_72768_72831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72832_72895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72832_72895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72832_72895 :
    ∀ i : Fin 64, indexedBlockCheck (72832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72832 0 32 h0 checkBlocks_72832_72895_part0
  have h64 := extendCertifiedSegment 72832 32 32 h32 checkBlocks_72832_72895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72896_72959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72896_72959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72896_72959 :
    ∀ i : Fin 64, indexedBlockCheck (72896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72896 0 32 h0 checkBlocks_72896_72959_part0
  have h64 := extendCertifiedSegment 72896 32 32 h32 checkBlocks_72896_72959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72960_73023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (72960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72960_73023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (72992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72960_73023 :
    ∀ i : Fin 64, indexedBlockCheck (72960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 72960 0 32 h0 checkBlocks_72960_73023_part0
  have h64 := extendCertifiedSegment 72960 32 32 h32 checkBlocks_72960_73023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73024_73087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73024_73087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73024_73087 :
    ∀ i : Fin 64, indexedBlockCheck (73024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73024 0 32 h0 checkBlocks_73024_73087_part0
  have h64 := extendCertifiedSegment 73024 32 32 h32 checkBlocks_73024_73087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73088_73151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73088_73151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73088_73151 :
    ∀ i : Fin 64, indexedBlockCheck (73088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73088 0 32 h0 checkBlocks_73088_73151_part0
  have h64 := extendCertifiedSegment 73088 32 32 h32 checkBlocks_73088_73151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73152_73215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73152_73215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73152_73215 :
    ∀ i : Fin 64, indexedBlockCheck (73152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73152 0 32 h0 checkBlocks_73152_73215_part0
  have h64 := extendCertifiedSegment 73152 32 32 h32 checkBlocks_73152_73215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_72704_73215 :
    ∀ i : Fin 512, indexedBlockCheck (72704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72704 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 72704 0 64 h0 checkBlocks_72704_72767
  have h128 := extendCertifiedSegment 72704 64 64 h64 checkBlocks_72768_72831
  have h192 := extendCertifiedSegment 72704 128 64 h128 checkBlocks_72832_72895
  have h256 := extendCertifiedSegment 72704 192 64 h192 checkBlocks_72896_72959
  have h320 := extendCertifiedSegment 72704 256 64 h256 checkBlocks_72960_73023
  have h384 := extendCertifiedSegment 72704 320 64 h320 checkBlocks_73024_73087
  have h448 := extendCertifiedSegment 72704 384 64 h384 checkBlocks_73088_73151
  have h512 := extendCertifiedSegment 72704 448 64 h448 checkBlocks_73152_73215
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_73216_73279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73216_73279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73216_73279 :
    ∀ i : Fin 64, indexedBlockCheck (73216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73216 0 32 h0 checkBlocks_73216_73279_part0
  have h64 := extendCertifiedSegment 73216 32 32 h32 checkBlocks_73216_73279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73280_73343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73280_73343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73280_73343 :
    ∀ i : Fin 64, indexedBlockCheck (73280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73280 0 32 h0 checkBlocks_73280_73343_part0
  have h64 := extendCertifiedSegment 73280 32 32 h32 checkBlocks_73280_73343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73344_73407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73344_73407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73344_73407 :
    ∀ i : Fin 64, indexedBlockCheck (73344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73344 0 32 h0 checkBlocks_73344_73407_part0
  have h64 := extendCertifiedSegment 73344 32 32 h32 checkBlocks_73344_73407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73408_73471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73408_73471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73408_73471 :
    ∀ i : Fin 64, indexedBlockCheck (73408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73408 0 32 h0 checkBlocks_73408_73471_part0
  have h64 := extendCertifiedSegment 73408 32 32 h32 checkBlocks_73408_73471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73472_73535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73472_73535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73472_73535 :
    ∀ i : Fin 64, indexedBlockCheck (73472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73472 0 32 h0 checkBlocks_73472_73535_part0
  have h64 := extendCertifiedSegment 73472 32 32 h32 checkBlocks_73472_73535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73536_73599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73536_73599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73536_73599 :
    ∀ i : Fin 64, indexedBlockCheck (73536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73536 0 32 h0 checkBlocks_73536_73599_part0
  have h64 := extendCertifiedSegment 73536 32 32 h32 checkBlocks_73536_73599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73600_73663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73600_73663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73600_73663 :
    ∀ i : Fin 64, indexedBlockCheck (73600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73600 0 32 h0 checkBlocks_73600_73663_part0
  have h64 := extendCertifiedSegment 73600 32 32 h32 checkBlocks_73600_73663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73664_73727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73664_73727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73664_73727 :
    ∀ i : Fin 64, indexedBlockCheck (73664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73664 0 32 h0 checkBlocks_73664_73727_part0
  have h64 := extendCertifiedSegment 73664 32 32 h32 checkBlocks_73664_73727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73216_73727 :
    ∀ i : Fin 512, indexedBlockCheck (73216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73216 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 73216 0 64 h0 checkBlocks_73216_73279
  have h128 := extendCertifiedSegment 73216 64 64 h64 checkBlocks_73280_73343
  have h192 := extendCertifiedSegment 73216 128 64 h128 checkBlocks_73344_73407
  have h256 := extendCertifiedSegment 73216 192 64 h192 checkBlocks_73408_73471
  have h320 := extendCertifiedSegment 73216 256 64 h256 checkBlocks_73472_73535
  have h384 := extendCertifiedSegment 73216 320 64 h320 checkBlocks_73536_73599
  have h448 := extendCertifiedSegment 73216 384 64 h384 checkBlocks_73600_73663
  have h512 := extendCertifiedSegment 73216 448 64 h448 checkBlocks_73664_73727
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_73728_73791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73728_73791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73728_73791 :
    ∀ i : Fin 64, indexedBlockCheck (73728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73728 0 32 h0 checkBlocks_73728_73791_part0
  have h64 := extendCertifiedSegment 73728 32 32 h32 checkBlocks_73728_73791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73792_73855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73792_73855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73792_73855 :
    ∀ i : Fin 64, indexedBlockCheck (73792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73792 0 32 h0 checkBlocks_73792_73855_part0
  have h64 := extendCertifiedSegment 73792 32 32 h32 checkBlocks_73792_73855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73856_73919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73856_73919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73856_73919 :
    ∀ i : Fin 64, indexedBlockCheck (73856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73856 0 32 h0 checkBlocks_73856_73919_part0
  have h64 := extendCertifiedSegment 73856 32 32 h32 checkBlocks_73856_73919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73920_73983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73920_73983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (73952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73920_73983 :
    ∀ i : Fin 64, indexedBlockCheck (73920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73920 0 32 h0 checkBlocks_73920_73983_part0
  have h64 := extendCertifiedSegment 73920 32 32 h32 checkBlocks_73920_73983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73984_74047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (73984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73984_74047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73984_74047 :
    ∀ i : Fin 64, indexedBlockCheck (73984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 73984 0 32 h0 checkBlocks_73984_74047_part0
  have h64 := extendCertifiedSegment 73984 32 32 h32 checkBlocks_73984_74047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74048_74111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74048_74111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74048_74111 :
    ∀ i : Fin 64, indexedBlockCheck (74048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74048 0 32 h0 checkBlocks_74048_74111_part0
  have h64 := extendCertifiedSegment 74048 32 32 h32 checkBlocks_74048_74111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74112_74175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74112_74175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74112_74175 :
    ∀ i : Fin 64, indexedBlockCheck (74112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74112 0 32 h0 checkBlocks_74112_74175_part0
  have h64 := extendCertifiedSegment 74112 32 32 h32 checkBlocks_74112_74175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74176_74239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74176_74239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74176_74239 :
    ∀ i : Fin 64, indexedBlockCheck (74176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74176 0 32 h0 checkBlocks_74176_74239_part0
  have h64 := extendCertifiedSegment 74176 32 32 h32 checkBlocks_74176_74239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_73728_74239 :
    ∀ i : Fin 512, indexedBlockCheck (73728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (73728 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 73728 0 64 h0 checkBlocks_73728_73791
  have h128 := extendCertifiedSegment 73728 64 64 h64 checkBlocks_73792_73855
  have h192 := extendCertifiedSegment 73728 128 64 h128 checkBlocks_73856_73919
  have h256 := extendCertifiedSegment 73728 192 64 h192 checkBlocks_73920_73983
  have h320 := extendCertifiedSegment 73728 256 64 h256 checkBlocks_73984_74047
  have h384 := extendCertifiedSegment 73728 320 64 h320 checkBlocks_74048_74111
  have h448 := extendCertifiedSegment 73728 384 64 h384 checkBlocks_74112_74175
  have h512 := extendCertifiedSegment 73728 448 64 h448 checkBlocks_74176_74239
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_74240_74303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74240_74303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74240_74303 :
    ∀ i : Fin 64, indexedBlockCheck (74240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74240 0 32 h0 checkBlocks_74240_74303_part0
  have h64 := extendCertifiedSegment 74240 32 32 h32 checkBlocks_74240_74303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74304_74367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74304_74367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74304_74367 :
    ∀ i : Fin 64, indexedBlockCheck (74304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74304 0 32 h0 checkBlocks_74304_74367_part0
  have h64 := extendCertifiedSegment 74304 32 32 h32 checkBlocks_74304_74367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74368_74431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74368_74431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74368_74431 :
    ∀ i : Fin 64, indexedBlockCheck (74368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74368 0 32 h0 checkBlocks_74368_74431_part0
  have h64 := extendCertifiedSegment 74368 32 32 h32 checkBlocks_74368_74431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74432_74495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74432_74495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74432_74495 :
    ∀ i : Fin 64, indexedBlockCheck (74432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74432 0 32 h0 checkBlocks_74432_74495_part0
  have h64 := extendCertifiedSegment 74432 32 32 h32 checkBlocks_74432_74495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74496_74559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74496_74559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74496_74559 :
    ∀ i : Fin 64, indexedBlockCheck (74496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74496 0 32 h0 checkBlocks_74496_74559_part0
  have h64 := extendCertifiedSegment 74496 32 32 h32 checkBlocks_74496_74559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74560_74623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74560_74623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74560_74623 :
    ∀ i : Fin 64, indexedBlockCheck (74560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74560 0 32 h0 checkBlocks_74560_74623_part0
  have h64 := extendCertifiedSegment 74560 32 32 h32 checkBlocks_74560_74623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74624_74687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74624_74687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74624_74687 :
    ∀ i : Fin 64, indexedBlockCheck (74624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74624 0 32 h0 checkBlocks_74624_74687_part0
  have h64 := extendCertifiedSegment 74624 32 32 h32 checkBlocks_74624_74687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74688_74751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (74688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74688_74751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (74720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74688_74751 :
    ∀ i : Fin 64, indexedBlockCheck (74688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 74688 0 32 h0 checkBlocks_74688_74751_part0
  have h64 := extendCertifiedSegment 74688 32 32 h32 checkBlocks_74688_74751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_74240_74751 :
    ∀ i : Fin 512, indexedBlockCheck (74240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (74240 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 74240 0 64 h0 checkBlocks_74240_74303
  have h128 := extendCertifiedSegment 74240 64 64 h64 checkBlocks_74304_74367
  have h192 := extendCertifiedSegment 74240 128 64 h128 checkBlocks_74368_74431
  have h256 := extendCertifiedSegment 74240 192 64 h192 checkBlocks_74432_74495
  have h320 := extendCertifiedSegment 74240 256 64 h256 checkBlocks_74496_74559
  have h384 := extendCertifiedSegment 74240 320 64 h320 checkBlocks_74560_74623
  have h448 := extendCertifiedSegment 74240 384 64 h384 checkBlocks_74624_74687
  have h512 := extendCertifiedSegment 74240 448 64 h448 checkBlocks_74688_74751
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [72704, 74752) passes the packed checker. -/
public theorem blocks_in_72704_74752 :
    ∀ i : Fin 2048, indexedBlockCheck (72704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72704 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 72704 0 512 h0 checkBlocks_72704_73215
  have h1024 := extendCertifiedSegment 72704 512 512 h512 checkBlocks_73216_73727
  have h1536 := extendCertifiedSegment 72704 1024 512 h1024 checkBlocks_73728_74239
  have h2048 := extendCertifiedSegment 72704 1536 512 h1536 checkBlocks_74240_74751
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
