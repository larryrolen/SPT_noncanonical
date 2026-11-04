/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 1024 through 3071 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_1024_1087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1024_1087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1024_1087 :
    ∀ i : Fin 64, indexedBlockCheck (1024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1024 0 32 h0 checkBlocks_1024_1087_part0
  have h64 := extendCertifiedSegment 1024 32 32 h32 checkBlocks_1024_1087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1088_1151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1088_1151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1088_1151 :
    ∀ i : Fin 64, indexedBlockCheck (1088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1088 0 32 h0 checkBlocks_1088_1151_part0
  have h64 := extendCertifiedSegment 1088 32 32 h32 checkBlocks_1088_1151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1152_1215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1152_1215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1152_1215 :
    ∀ i : Fin 64, indexedBlockCheck (1152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1152 0 32 h0 checkBlocks_1152_1215_part0
  have h64 := extendCertifiedSegment 1152 32 32 h32 checkBlocks_1152_1215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1216_1279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1216_1279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1216_1279 :
    ∀ i : Fin 64, indexedBlockCheck (1216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1216 0 32 h0 checkBlocks_1216_1279_part0
  have h64 := extendCertifiedSegment 1216 32 32 h32 checkBlocks_1216_1279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1280_1343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1280_1343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1280_1343 :
    ∀ i : Fin 64, indexedBlockCheck (1280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1280 0 32 h0 checkBlocks_1280_1343_part0
  have h64 := extendCertifiedSegment 1280 32 32 h32 checkBlocks_1280_1343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1344_1407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1344_1407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1344_1407 :
    ∀ i : Fin 64, indexedBlockCheck (1344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1344 0 32 h0 checkBlocks_1344_1407_part0
  have h64 := extendCertifiedSegment 1344 32 32 h32 checkBlocks_1344_1407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1408_1471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1408_1471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1408_1471 :
    ∀ i : Fin 64, indexedBlockCheck (1408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1408 0 32 h0 checkBlocks_1408_1471_part0
  have h64 := extendCertifiedSegment 1408 32 32 h32 checkBlocks_1408_1471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1472_1535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1472_1535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1472_1535 :
    ∀ i : Fin 64, indexedBlockCheck (1472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1472 0 32 h0 checkBlocks_1472_1535_part0
  have h64 := extendCertifiedSegment 1472 32 32 h32 checkBlocks_1472_1535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1024_1535 :
    ∀ i : Fin 512, indexedBlockCheck (1024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1024 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 1024 0 64 h0 checkBlocks_1024_1087
  have h128 := extendCertifiedSegment 1024 64 64 h64 checkBlocks_1088_1151
  have h192 := extendCertifiedSegment 1024 128 64 h128 checkBlocks_1152_1215
  have h256 := extendCertifiedSegment 1024 192 64 h192 checkBlocks_1216_1279
  have h320 := extendCertifiedSegment 1024 256 64 h256 checkBlocks_1280_1343
  have h384 := extendCertifiedSegment 1024 320 64 h320 checkBlocks_1344_1407
  have h448 := extendCertifiedSegment 1024 384 64 h384 checkBlocks_1408_1471
  have h512 := extendCertifiedSegment 1024 448 64 h448 checkBlocks_1472_1535
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_1536_1599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1536_1599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1536_1599 :
    ∀ i : Fin 64, indexedBlockCheck (1536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1536 0 32 h0 checkBlocks_1536_1599_part0
  have h64 := extendCertifiedSegment 1536 32 32 h32 checkBlocks_1536_1599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1600_1663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1600_1663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1600_1663 :
    ∀ i : Fin 64, indexedBlockCheck (1600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1600 0 32 h0 checkBlocks_1600_1663_part0
  have h64 := extendCertifiedSegment 1600 32 32 h32 checkBlocks_1600_1663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1664_1727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1664_1727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1664_1727 :
    ∀ i : Fin 64, indexedBlockCheck (1664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1664 0 32 h0 checkBlocks_1664_1727_part0
  have h64 := extendCertifiedSegment 1664 32 32 h32 checkBlocks_1664_1727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1728_1791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1728_1791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1728_1791 :
    ∀ i : Fin 64, indexedBlockCheck (1728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1728 0 32 h0 checkBlocks_1728_1791_part0
  have h64 := extendCertifiedSegment 1728 32 32 h32 checkBlocks_1728_1791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1792_1855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1792_1855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1792_1855 :
    ∀ i : Fin 64, indexedBlockCheck (1792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1792 0 32 h0 checkBlocks_1792_1855_part0
  have h64 := extendCertifiedSegment 1792 32 32 h32 checkBlocks_1792_1855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1856_1919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1856_1919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1856_1919 :
    ∀ i : Fin 64, indexedBlockCheck (1856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1856 0 32 h0 checkBlocks_1856_1919_part0
  have h64 := extendCertifiedSegment 1856 32 32 h32 checkBlocks_1856_1919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1920_1983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1920_1983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (1952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1920_1983 :
    ∀ i : Fin 64, indexedBlockCheck (1920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1920 0 32 h0 checkBlocks_1920_1983_part0
  have h64 := extendCertifiedSegment 1920 32 32 h32 checkBlocks_1920_1983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1984_2047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (1984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1984_2047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_1984_2047 :
    ∀ i : Fin 64, indexedBlockCheck (1984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 1984 0 32 h0 checkBlocks_1984_2047_part0
  have h64 := extendCertifiedSegment 1984 32 32 h32 checkBlocks_1984_2047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_1536_2047 :
    ∀ i : Fin 512, indexedBlockCheck (1536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1536 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 1536 0 64 h0 checkBlocks_1536_1599
  have h128 := extendCertifiedSegment 1536 64 64 h64 checkBlocks_1600_1663
  have h192 := extendCertifiedSegment 1536 128 64 h128 checkBlocks_1664_1727
  have h256 := extendCertifiedSegment 1536 192 64 h192 checkBlocks_1728_1791
  have h320 := extendCertifiedSegment 1536 256 64 h256 checkBlocks_1792_1855
  have h384 := extendCertifiedSegment 1536 320 64 h320 checkBlocks_1856_1919
  have h448 := extendCertifiedSegment 1536 384 64 h384 checkBlocks_1920_1983
  have h512 := extendCertifiedSegment 1536 448 64 h448 checkBlocks_1984_2047
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_2048_2111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2048_2111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2048_2111 :
    ∀ i : Fin 64, indexedBlockCheck (2048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2048 0 32 h0 checkBlocks_2048_2111_part0
  have h64 := extendCertifiedSegment 2048 32 32 h32 checkBlocks_2048_2111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2112_2175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2112_2175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2112_2175 :
    ∀ i : Fin 64, indexedBlockCheck (2112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2112 0 32 h0 checkBlocks_2112_2175_part0
  have h64 := extendCertifiedSegment 2112 32 32 h32 checkBlocks_2112_2175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2176_2239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2176_2239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2176_2239 :
    ∀ i : Fin 64, indexedBlockCheck (2176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2176 0 32 h0 checkBlocks_2176_2239_part0
  have h64 := extendCertifiedSegment 2176 32 32 h32 checkBlocks_2176_2239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2240_2303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2240_2303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2240_2303 :
    ∀ i : Fin 64, indexedBlockCheck (2240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2240 0 32 h0 checkBlocks_2240_2303_part0
  have h64 := extendCertifiedSegment 2240 32 32 h32 checkBlocks_2240_2303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2304_2367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2304_2367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2304_2367 :
    ∀ i : Fin 64, indexedBlockCheck (2304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2304 0 32 h0 checkBlocks_2304_2367_part0
  have h64 := extendCertifiedSegment 2304 32 32 h32 checkBlocks_2304_2367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2368_2431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2368_2431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2368_2431 :
    ∀ i : Fin 64, indexedBlockCheck (2368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2368 0 32 h0 checkBlocks_2368_2431_part0
  have h64 := extendCertifiedSegment 2368 32 32 h32 checkBlocks_2368_2431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2432_2495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2432_2495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2432_2495 :
    ∀ i : Fin 64, indexedBlockCheck (2432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2432 0 32 h0 checkBlocks_2432_2495_part0
  have h64 := extendCertifiedSegment 2432 32 32 h32 checkBlocks_2432_2495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2496_2559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2496_2559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2496_2559 :
    ∀ i : Fin 64, indexedBlockCheck (2496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2496 0 32 h0 checkBlocks_2496_2559_part0
  have h64 := extendCertifiedSegment 2496 32 32 h32 checkBlocks_2496_2559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2048_2559 :
    ∀ i : Fin 512, indexedBlockCheck (2048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2048 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 2048 0 64 h0 checkBlocks_2048_2111
  have h128 := extendCertifiedSegment 2048 64 64 h64 checkBlocks_2112_2175
  have h192 := extendCertifiedSegment 2048 128 64 h128 checkBlocks_2176_2239
  have h256 := extendCertifiedSegment 2048 192 64 h192 checkBlocks_2240_2303
  have h320 := extendCertifiedSegment 2048 256 64 h256 checkBlocks_2304_2367
  have h384 := extendCertifiedSegment 2048 320 64 h320 checkBlocks_2368_2431
  have h448 := extendCertifiedSegment 2048 384 64 h384 checkBlocks_2432_2495
  have h512 := extendCertifiedSegment 2048 448 64 h448 checkBlocks_2496_2559
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_2560_2623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2560_2623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2560_2623 :
    ∀ i : Fin 64, indexedBlockCheck (2560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2560 0 32 h0 checkBlocks_2560_2623_part0
  have h64 := extendCertifiedSegment 2560 32 32 h32 checkBlocks_2560_2623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2624_2687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2624_2687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2624_2687 :
    ∀ i : Fin 64, indexedBlockCheck (2624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2624 0 32 h0 checkBlocks_2624_2687_part0
  have h64 := extendCertifiedSegment 2624 32 32 h32 checkBlocks_2624_2687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2688_2751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2688_2751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2688_2751 :
    ∀ i : Fin 64, indexedBlockCheck (2688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2688 0 32 h0 checkBlocks_2688_2751_part0
  have h64 := extendCertifiedSegment 2688 32 32 h32 checkBlocks_2688_2751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2752_2815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2752_2815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2752_2815 :
    ∀ i : Fin 64, indexedBlockCheck (2752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2752 0 32 h0 checkBlocks_2752_2815_part0
  have h64 := extendCertifiedSegment 2752 32 32 h32 checkBlocks_2752_2815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2816_2879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2816_2879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2816_2879 :
    ∀ i : Fin 64, indexedBlockCheck (2816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2816 0 32 h0 checkBlocks_2816_2879_part0
  have h64 := extendCertifiedSegment 2816 32 32 h32 checkBlocks_2816_2879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2880_2943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2880_2943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2880_2943 :
    ∀ i : Fin 64, indexedBlockCheck (2880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2880 0 32 h0 checkBlocks_2880_2943_part0
  have h64 := extendCertifiedSegment 2880 32 32 h32 checkBlocks_2880_2943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2944_3007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (2944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2944_3007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (2976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_2944_3007 :
    ∀ i : Fin 64, indexedBlockCheck (2944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 2944 0 32 h0 checkBlocks_2944_3007_part0
  have h64 := extendCertifiedSegment 2944 32 32 h32 checkBlocks_2944_3007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_3008_3071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (3008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3008_3071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (3040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_3008_3071 :
    ∀ i : Fin 64, indexedBlockCheck (3008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (3008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 3008 0 32 h0 checkBlocks_3008_3071_part0
  have h64 := extendCertifiedSegment 3008 32 32 h32 checkBlocks_3008_3071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_2560_3071 :
    ∀ i : Fin 512, indexedBlockCheck (2560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (2560 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 2560 0 64 h0 checkBlocks_2560_2623
  have h128 := extendCertifiedSegment 2560 64 64 h64 checkBlocks_2624_2687
  have h192 := extendCertifiedSegment 2560 128 64 h128 checkBlocks_2688_2751
  have h256 := extendCertifiedSegment 2560 192 64 h192 checkBlocks_2752_2815
  have h320 := extendCertifiedSegment 2560 256 64 h256 checkBlocks_2816_2879
  have h384 := extendCertifiedSegment 2560 320 64 h320 checkBlocks_2880_2943
  have h448 := extendCertifiedSegment 2560 384 64 h384 checkBlocks_2944_3007
  have h512 := extendCertifiedSegment 2560 448 64 h448 checkBlocks_3008_3071
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [1024, 3072) passes the packed checker. -/
public theorem blocks_in_1024_3072 :
    ∀ i : Fin 2048, indexedBlockCheck (1024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (1024 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 1024 0 512 h0 checkBlocks_1024_1535
  have h1024 := extendCertifiedSegment 1024 512 512 h512 checkBlocks_1536_2047
  have h1536 := extendCertifiedSegment 1024 1024 512 h1024 checkBlocks_2048_2559
  have h2048 := extendCertifiedSegment 1024 1536 512 h1536 checkBlocks_2560_3071
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
