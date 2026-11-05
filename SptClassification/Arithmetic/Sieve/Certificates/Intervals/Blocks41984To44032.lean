/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 41984 through 44031 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_41984_42047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (41984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41984_42047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41984_42047 :
    ∀ i : Fin 64, indexedBlockCheck (41984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 41984 0 32 h0 checkBlocks_41984_42047_part0
  have h64 := extendCertifiedSegment 41984 32 32 h32 checkBlocks_41984_42047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42048_42111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42048_42111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42048_42111 :
    ∀ i : Fin 64, indexedBlockCheck (42048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42048 0 32 h0 checkBlocks_42048_42111_part0
  have h64 := extendCertifiedSegment 42048 32 32 h32 checkBlocks_42048_42111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42112_42175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42112_42175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42112_42175 :
    ∀ i : Fin 64, indexedBlockCheck (42112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42112 0 32 h0 checkBlocks_42112_42175_part0
  have h64 := extendCertifiedSegment 42112 32 32 h32 checkBlocks_42112_42175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42176_42239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42176_42239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42176_42239 :
    ∀ i : Fin 64, indexedBlockCheck (42176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42176 0 32 h0 checkBlocks_42176_42239_part0
  have h64 := extendCertifiedSegment 42176 32 32 h32 checkBlocks_42176_42239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42240_42303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42240_42303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42240_42303 :
    ∀ i : Fin 64, indexedBlockCheck (42240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42240 0 32 h0 checkBlocks_42240_42303_part0
  have h64 := extendCertifiedSegment 42240 32 32 h32 checkBlocks_42240_42303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42304_42367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42304_42367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42304_42367 :
    ∀ i : Fin 64, indexedBlockCheck (42304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42304 0 32 h0 checkBlocks_42304_42367_part0
  have h64 := extendCertifiedSegment 42304 32 32 h32 checkBlocks_42304_42367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42368_42431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42368_42431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42368_42431 :
    ∀ i : Fin 64, indexedBlockCheck (42368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42368 0 32 h0 checkBlocks_42368_42431_part0
  have h64 := extendCertifiedSegment 42368 32 32 h32 checkBlocks_42368_42431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42432_42495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42432_42495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42432_42495 :
    ∀ i : Fin 64, indexedBlockCheck (42432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42432 0 32 h0 checkBlocks_42432_42495_part0
  have h64 := extendCertifiedSegment 42432 32 32 h32 checkBlocks_42432_42495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_41984_42495 :
    ∀ i : Fin 512, indexedBlockCheck (41984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41984 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 41984 0 64 h0 checkBlocks_41984_42047
  have h128 := extendCertifiedSegment 41984 64 64 h64 checkBlocks_42048_42111
  have h192 := extendCertifiedSegment 41984 128 64 h128 checkBlocks_42112_42175
  have h256 := extendCertifiedSegment 41984 192 64 h192 checkBlocks_42176_42239
  have h320 := extendCertifiedSegment 41984 256 64 h256 checkBlocks_42240_42303
  have h384 := extendCertifiedSegment 41984 320 64 h320 checkBlocks_42304_42367
  have h448 := extendCertifiedSegment 41984 384 64 h384 checkBlocks_42368_42431
  have h512 := extendCertifiedSegment 41984 448 64 h448 checkBlocks_42432_42495
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_42496_42559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42496_42559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42496_42559 :
    ∀ i : Fin 64, indexedBlockCheck (42496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42496 0 32 h0 checkBlocks_42496_42559_part0
  have h64 := extendCertifiedSegment 42496 32 32 h32 checkBlocks_42496_42559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42560_42623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42560_42623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42560_42623 :
    ∀ i : Fin 64, indexedBlockCheck (42560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42560 0 32 h0 checkBlocks_42560_42623_part0
  have h64 := extendCertifiedSegment 42560 32 32 h32 checkBlocks_42560_42623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42624_42687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42624_42687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42624_42687 :
    ∀ i : Fin 64, indexedBlockCheck (42624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42624 0 32 h0 checkBlocks_42624_42687_part0
  have h64 := extendCertifiedSegment 42624 32 32 h32 checkBlocks_42624_42687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42688_42751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42688_42751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42688_42751 :
    ∀ i : Fin 64, indexedBlockCheck (42688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42688 0 32 h0 checkBlocks_42688_42751_part0
  have h64 := extendCertifiedSegment 42688 32 32 h32 checkBlocks_42688_42751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42752_42815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42752_42815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42752_42815 :
    ∀ i : Fin 64, indexedBlockCheck (42752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42752 0 32 h0 checkBlocks_42752_42815_part0
  have h64 := extendCertifiedSegment 42752 32 32 h32 checkBlocks_42752_42815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42816_42879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42816_42879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42816_42879 :
    ∀ i : Fin 64, indexedBlockCheck (42816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42816 0 32 h0 checkBlocks_42816_42879_part0
  have h64 := extendCertifiedSegment 42816 32 32 h32 checkBlocks_42816_42879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42880_42943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42880_42943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42880_42943 :
    ∀ i : Fin 64, indexedBlockCheck (42880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42880 0 32 h0 checkBlocks_42880_42943_part0
  have h64 := extendCertifiedSegment 42880 32 32 h32 checkBlocks_42880_42943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42944_43007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (42944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42944_43007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (42976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42944_43007 :
    ∀ i : Fin 64, indexedBlockCheck (42944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 42944 0 32 h0 checkBlocks_42944_43007_part0
  have h64 := extendCertifiedSegment 42944 32 32 h32 checkBlocks_42944_43007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_42496_43007 :
    ∀ i : Fin 512, indexedBlockCheck (42496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42496 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 42496 0 64 h0 checkBlocks_42496_42559
  have h128 := extendCertifiedSegment 42496 64 64 h64 checkBlocks_42560_42623
  have h192 := extendCertifiedSegment 42496 128 64 h128 checkBlocks_42624_42687
  have h256 := extendCertifiedSegment 42496 192 64 h192 checkBlocks_42688_42751
  have h320 := extendCertifiedSegment 42496 256 64 h256 checkBlocks_42752_42815
  have h384 := extendCertifiedSegment 42496 320 64 h320 checkBlocks_42816_42879
  have h448 := extendCertifiedSegment 42496 384 64 h384 checkBlocks_42880_42943
  have h512 := extendCertifiedSegment 42496 448 64 h448 checkBlocks_42944_43007
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_43008_43071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43008_43071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43008_43071 :
    ∀ i : Fin 64, indexedBlockCheck (43008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43008 0 32 h0 checkBlocks_43008_43071_part0
  have h64 := extendCertifiedSegment 43008 32 32 h32 checkBlocks_43008_43071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43072_43135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43072_43135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43072_43135 :
    ∀ i : Fin 64, indexedBlockCheck (43072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43072 0 32 h0 checkBlocks_43072_43135_part0
  have h64 := extendCertifiedSegment 43072 32 32 h32 checkBlocks_43072_43135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43136_43199_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43136_43199_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43136_43199 :
    ∀ i : Fin 64, indexedBlockCheck (43136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43136 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43136 0 32 h0 checkBlocks_43136_43199_part0
  have h64 := extendCertifiedSegment 43136 32 32 h32 checkBlocks_43136_43199_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43200_43263_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43200_43263_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43200_43263 :
    ∀ i : Fin 64, indexedBlockCheck (43200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43200 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43200 0 32 h0 checkBlocks_43200_43263_part0
  have h64 := extendCertifiedSegment 43200 32 32 h32 checkBlocks_43200_43263_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43264_43327_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43264_43327_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43264_43327 :
    ∀ i : Fin 64, indexedBlockCheck (43264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43264 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43264 0 32 h0 checkBlocks_43264_43327_part0
  have h64 := extendCertifiedSegment 43264 32 32 h32 checkBlocks_43264_43327_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43328_43391_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43328_43391_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43328_43391 :
    ∀ i : Fin 64, indexedBlockCheck (43328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43328 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43328 0 32 h0 checkBlocks_43328_43391_part0
  have h64 := extendCertifiedSegment 43328 32 32 h32 checkBlocks_43328_43391_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43392_43455_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43392_43455_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43392_43455 :
    ∀ i : Fin 64, indexedBlockCheck (43392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43392 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43392 0 32 h0 checkBlocks_43392_43455_part0
  have h64 := extendCertifiedSegment 43392 32 32 h32 checkBlocks_43392_43455_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43456_43519_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43456_43519_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43456_43519 :
    ∀ i : Fin 64, indexedBlockCheck (43456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43456 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43456 0 32 h0 checkBlocks_43456_43519_part0
  have h64 := extendCertifiedSegment 43456 32 32 h32 checkBlocks_43456_43519_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43008_43519 :
    ∀ i : Fin 512, indexedBlockCheck (43008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43008 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 43008 0 64 h0 checkBlocks_43008_43071
  have h128 := extendCertifiedSegment 43008 64 64 h64 checkBlocks_43072_43135
  have h192 := extendCertifiedSegment 43008 128 64 h128 checkBlocks_43136_43199
  have h256 := extendCertifiedSegment 43008 192 64 h192 checkBlocks_43200_43263
  have h320 := extendCertifiedSegment 43008 256 64 h256 checkBlocks_43264_43327
  have h384 := extendCertifiedSegment 43008 320 64 h320 checkBlocks_43328_43391
  have h448 := extendCertifiedSegment 43008 384 64 h384 checkBlocks_43392_43455
  have h512 := extendCertifiedSegment 43008 448 64 h448 checkBlocks_43456_43519
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_43520_43583_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43520_43583_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43520_43583 :
    ∀ i : Fin 64, indexedBlockCheck (43520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43520 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43520 0 32 h0 checkBlocks_43520_43583_part0
  have h64 := extendCertifiedSegment 43520 32 32 h32 checkBlocks_43520_43583_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43584_43647_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43584_43647_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43584_43647 :
    ∀ i : Fin 64, indexedBlockCheck (43584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43584 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43584 0 32 h0 checkBlocks_43584_43647_part0
  have h64 := extendCertifiedSegment 43584 32 32 h32 checkBlocks_43584_43647_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43648_43711_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43648_43711_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43648_43711 :
    ∀ i : Fin 64, indexedBlockCheck (43648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43648 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43648 0 32 h0 checkBlocks_43648_43711_part0
  have h64 := extendCertifiedSegment 43648 32 32 h32 checkBlocks_43648_43711_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43712_43775_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43712_43775_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43712_43775 :
    ∀ i : Fin 64, indexedBlockCheck (43712 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43712 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43712 0 32 h0 checkBlocks_43712_43775_part0
  have h64 := extendCertifiedSegment 43712 32 32 h32 checkBlocks_43712_43775_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43776_43839_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43776_43839_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43776_43839 :
    ∀ i : Fin 64, indexedBlockCheck (43776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43776 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43776 0 32 h0 checkBlocks_43776_43839_part0
  have h64 := extendCertifiedSegment 43776 32 32 h32 checkBlocks_43776_43839_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43840_43903_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43840_43903_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43840_43903 :
    ∀ i : Fin 64, indexedBlockCheck (43840 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43840 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43840 0 32 h0 checkBlocks_43840_43903_part0
  have h64 := extendCertifiedSegment 43840 32 32 h32 checkBlocks_43840_43903_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43904_43967_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43904_43967_part1 :
    ∀ i : Fin 32, indexedBlockCheck (43936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43904_43967 :
    ∀ i : Fin 64, indexedBlockCheck (43904 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43904 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43904 0 32 h0 checkBlocks_43904_43967_part0
  have h64 := extendCertifiedSegment 43904 32 32 h32 checkBlocks_43904_43967_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43968_44031_part0 :
    ∀ i : Fin 32, indexedBlockCheck (43968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43968_44031_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43968_44031 :
    ∀ i : Fin 64, indexedBlockCheck (43968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43968 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 43968 0 32 h0 checkBlocks_43968_44031_part0
  have h64 := extendCertifiedSegment 43968 32 32 h32 checkBlocks_43968_44031_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_43520_44031 :
    ∀ i : Fin 512, indexedBlockCheck (43520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43520 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 43520 0 64 h0 checkBlocks_43520_43583
  have h128 := extendCertifiedSegment 43520 64 64 h64 checkBlocks_43584_43647
  have h192 := extendCertifiedSegment 43520 128 64 h128 checkBlocks_43648_43711
  have h256 := extendCertifiedSegment 43520 192 64 h192 checkBlocks_43712_43775
  have h320 := extendCertifiedSegment 43520 256 64 h256 checkBlocks_43776_43839
  have h384 := extendCertifiedSegment 43520 320 64 h320 checkBlocks_43840_43903
  have h448 := extendCertifiedSegment 43520 384 64 h384 checkBlocks_43904_43967
  have h512 := extendCertifiedSegment 43520 448 64 h448 checkBlocks_43968_44031
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [41984, 44032) passes the packed checker. -/
public theorem blocks_in_41984_44032 :
    ∀ i : Fin 2048, indexedBlockCheck (41984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41984 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 41984 0 512 h0 checkBlocks_41984_42495
  have h1024 := extendCertifiedSegment 41984 512 512 h512 checkBlocks_42496_43007
  have h1536 := extendCertifiedSegment 41984 1024 512 h1024 checkBlocks_43008_43519
  have h2048 := extendCertifiedSegment 41984 1536 512 h1536 checkBlocks_43520_44031
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
