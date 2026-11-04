/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 72704 through 74751 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_72704_72767 :
    ∀ i : Fin 64, indexedBlockCheck (72704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72768_72831 :
    ∀ i : Fin 64, indexedBlockCheck (72768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72832_72895 :
    ∀ i : Fin 64, indexedBlockCheck (72832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72896_72959 :
    ∀ i : Fin 64, indexedBlockCheck (72896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72960_73023 :
    ∀ i : Fin 64, indexedBlockCheck (72960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73024_73087 :
    ∀ i : Fin 64, indexedBlockCheck (73024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73088_73151 :
    ∀ i : Fin 64, indexedBlockCheck (73088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73152_73215 :
    ∀ i : Fin 64, indexedBlockCheck (73152 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_73216_73279 :
    ∀ i : Fin 64, indexedBlockCheck (73216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73280_73343 :
    ∀ i : Fin 64, indexedBlockCheck (73280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73344_73407 :
    ∀ i : Fin 64, indexedBlockCheck (73344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73408_73471 :
    ∀ i : Fin 64, indexedBlockCheck (73408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73472_73535 :
    ∀ i : Fin 64, indexedBlockCheck (73472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73536_73599 :
    ∀ i : Fin 64, indexedBlockCheck (73536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73600_73663 :
    ∀ i : Fin 64, indexedBlockCheck (73600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73664_73727 :
    ∀ i : Fin 64, indexedBlockCheck (73664 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_73728_73791 :
    ∀ i : Fin 64, indexedBlockCheck (73728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73792_73855 :
    ∀ i : Fin 64, indexedBlockCheck (73792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73856_73919 :
    ∀ i : Fin 64, indexedBlockCheck (73856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73920_73983 :
    ∀ i : Fin 64, indexedBlockCheck (73920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_73984_74047 :
    ∀ i : Fin 64, indexedBlockCheck (73984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74048_74111 :
    ∀ i : Fin 64, indexedBlockCheck (74048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74112_74175 :
    ∀ i : Fin 64, indexedBlockCheck (74112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74176_74239 :
    ∀ i : Fin 64, indexedBlockCheck (74176 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_74240_74303 :
    ∀ i : Fin 64, indexedBlockCheck (74240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74304_74367 :
    ∀ i : Fin 64, indexedBlockCheck (74304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74368_74431 :
    ∀ i : Fin 64, indexedBlockCheck (74368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74432_74495 :
    ∀ i : Fin 64, indexedBlockCheck (74432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74496_74559 :
    ∀ i : Fin 64, indexedBlockCheck (74496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74560_74623 :
    ∀ i : Fin 64, indexedBlockCheck (74560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74624_74687 :
    ∀ i : Fin 64, indexedBlockCheck (74624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_74688_74751 :
    ∀ i : Fin 64, indexedBlockCheck (74688 + i.val) = true := by
  decide +kernel

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
