/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 33792 through 35839 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_33792_33855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33792_33855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33792_33855 :
    ∀ i : Fin 64, indexedBlockCheck (33792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33792 0 32 h0 checkBlocks_33792_33855_part0
  have h64 := extendCertifiedSegment 33792 32 32 h32 checkBlocks_33792_33855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33856_33919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33856_33919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33856_33919 :
    ∀ i : Fin 64, indexedBlockCheck (33856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33856 0 32 h0 checkBlocks_33856_33919_part0
  have h64 := extendCertifiedSegment 33856 32 32 h32 checkBlocks_33856_33919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33920_33983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33920_33983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (33952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33920_33983 :
    ∀ i : Fin 64, indexedBlockCheck (33920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33920 0 32 h0 checkBlocks_33920_33983_part0
  have h64 := extendCertifiedSegment 33920 32 32 h32 checkBlocks_33920_33983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33984_34047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (33984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33984_34047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_33984_34047 :
    ∀ i : Fin 64, indexedBlockCheck (33984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 33984 0 32 h0 checkBlocks_33984_34047_part0
  have h64 := extendCertifiedSegment 33984 32 32 h32 checkBlocks_33984_34047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34048_34111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34048_34111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34048_34111 :
    ∀ i : Fin 64, indexedBlockCheck (34048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34048 0 32 h0 checkBlocks_34048_34111_part0
  have h64 := extendCertifiedSegment 34048 32 32 h32 checkBlocks_34048_34111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34112_34175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34112_34175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34112_34175 :
    ∀ i : Fin 64, indexedBlockCheck (34112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34112 0 32 h0 checkBlocks_34112_34175_part0
  have h64 := extendCertifiedSegment 34112 32 32 h32 checkBlocks_34112_34175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34176_34239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34176_34239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34176_34239 :
    ∀ i : Fin 64, indexedBlockCheck (34176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34176 0 32 h0 checkBlocks_34176_34239_part0
  have h64 := extendCertifiedSegment 34176 32 32 h32 checkBlocks_34176_34239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34240_34303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34240_34303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34240_34303 :
    ∀ i : Fin 64, indexedBlockCheck (34240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34240 0 32 h0 checkBlocks_34240_34303_part0
  have h64 := extendCertifiedSegment 34240 32 32 h32 checkBlocks_34240_34303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_33792_34303 :
    ∀ i : Fin 512, indexedBlockCheck (33792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33792 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 33792 0 64 h0 checkBlocks_33792_33855
  have h128 := extendCertifiedSegment 33792 64 64 h64 checkBlocks_33856_33919
  have h192 := extendCertifiedSegment 33792 128 64 h128 checkBlocks_33920_33983
  have h256 := extendCertifiedSegment 33792 192 64 h192 checkBlocks_33984_34047
  have h320 := extendCertifiedSegment 33792 256 64 h256 checkBlocks_34048_34111
  have h384 := extendCertifiedSegment 33792 320 64 h320 checkBlocks_34112_34175
  have h448 := extendCertifiedSegment 33792 384 64 h384 checkBlocks_34176_34239
  have h512 := extendCertifiedSegment 33792 448 64 h448 checkBlocks_34240_34303
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_34304_34367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34304_34367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34304_34367 :
    ∀ i : Fin 64, indexedBlockCheck (34304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34304 0 32 h0 checkBlocks_34304_34367_part0
  have h64 := extendCertifiedSegment 34304 32 32 h32 checkBlocks_34304_34367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34368_34431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34368_34431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34368_34431 :
    ∀ i : Fin 64, indexedBlockCheck (34368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34368 0 32 h0 checkBlocks_34368_34431_part0
  have h64 := extendCertifiedSegment 34368 32 32 h32 checkBlocks_34368_34431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34432_34495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34432_34495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34432_34495 :
    ∀ i : Fin 64, indexedBlockCheck (34432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34432 0 32 h0 checkBlocks_34432_34495_part0
  have h64 := extendCertifiedSegment 34432 32 32 h32 checkBlocks_34432_34495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34496_34559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34496_34559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34496_34559 :
    ∀ i : Fin 64, indexedBlockCheck (34496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34496 0 32 h0 checkBlocks_34496_34559_part0
  have h64 := extendCertifiedSegment 34496 32 32 h32 checkBlocks_34496_34559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34560_34623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34560_34623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34560_34623 :
    ∀ i : Fin 64, indexedBlockCheck (34560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34560 0 32 h0 checkBlocks_34560_34623_part0
  have h64 := extendCertifiedSegment 34560 32 32 h32 checkBlocks_34560_34623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34624_34687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34624_34687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34624_34687 :
    ∀ i : Fin 64, indexedBlockCheck (34624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34624 0 32 h0 checkBlocks_34624_34687_part0
  have h64 := extendCertifiedSegment 34624 32 32 h32 checkBlocks_34624_34687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34688_34751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34688_34751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34688_34751 :
    ∀ i : Fin 64, indexedBlockCheck (34688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34688 0 32 h0 checkBlocks_34688_34751_part0
  have h64 := extendCertifiedSegment 34688 32 32 h32 checkBlocks_34688_34751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34752_34815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34752_34815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34752_34815 :
    ∀ i : Fin 64, indexedBlockCheck (34752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34752 0 32 h0 checkBlocks_34752_34815_part0
  have h64 := extendCertifiedSegment 34752 32 32 h32 checkBlocks_34752_34815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34304_34815 :
    ∀ i : Fin 512, indexedBlockCheck (34304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34304 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 34304 0 64 h0 checkBlocks_34304_34367
  have h128 := extendCertifiedSegment 34304 64 64 h64 checkBlocks_34368_34431
  have h192 := extendCertifiedSegment 34304 128 64 h128 checkBlocks_34432_34495
  have h256 := extendCertifiedSegment 34304 192 64 h192 checkBlocks_34496_34559
  have h320 := extendCertifiedSegment 34304 256 64 h256 checkBlocks_34560_34623
  have h384 := extendCertifiedSegment 34304 320 64 h320 checkBlocks_34624_34687
  have h448 := extendCertifiedSegment 34304 384 64 h384 checkBlocks_34688_34751
  have h512 := extendCertifiedSegment 34304 448 64 h448 checkBlocks_34752_34815
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_34816_34879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34816_34879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34816_34879 :
    ∀ i : Fin 64, indexedBlockCheck (34816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34816 0 32 h0 checkBlocks_34816_34879_part0
  have h64 := extendCertifiedSegment 34816 32 32 h32 checkBlocks_34816_34879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34880_34943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34880_34943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34880_34943 :
    ∀ i : Fin 64, indexedBlockCheck (34880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34880 0 32 h0 checkBlocks_34880_34943_part0
  have h64 := extendCertifiedSegment 34880 32 32 h32 checkBlocks_34880_34943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34944_35007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (34944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34944_35007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (34976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_34944_35007 :
    ∀ i : Fin 64, indexedBlockCheck (34944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 34944 0 32 h0 checkBlocks_34944_35007_part0
  have h64 := extendCertifiedSegment 34944 32 32 h32 checkBlocks_34944_35007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35008_35071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35008_35071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35008_35071 :
    ∀ i : Fin 64, indexedBlockCheck (35008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35008 0 32 h0 checkBlocks_35008_35071_part0
  have h64 := extendCertifiedSegment 35008 32 32 h32 checkBlocks_35008_35071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35072_35135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35072_35135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35072_35135 :
    ∀ i : Fin 64, indexedBlockCheck (35072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35072 0 32 h0 checkBlocks_35072_35135_part0
  have h64 := extendCertifiedSegment 35072 32 32 h32 checkBlocks_35072_35135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35136_35199_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35136_35199_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35136_35199 :
    ∀ i : Fin 64, indexedBlockCheck (35136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35136 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35136 0 32 h0 checkBlocks_35136_35199_part0
  have h64 := extendCertifiedSegment 35136 32 32 h32 checkBlocks_35136_35199_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35200_35263_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35200_35263_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35200_35263 :
    ∀ i : Fin 64, indexedBlockCheck (35200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35200 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35200 0 32 h0 checkBlocks_35200_35263_part0
  have h64 := extendCertifiedSegment 35200 32 32 h32 checkBlocks_35200_35263_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35264_35327_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35264_35327_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35264_35327 :
    ∀ i : Fin 64, indexedBlockCheck (35264 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35264 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35264 0 32 h0 checkBlocks_35264_35327_part0
  have h64 := extendCertifiedSegment 35264 32 32 h32 checkBlocks_35264_35327_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_34816_35327 :
    ∀ i : Fin 512, indexedBlockCheck (34816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (34816 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 34816 0 64 h0 checkBlocks_34816_34879
  have h128 := extendCertifiedSegment 34816 64 64 h64 checkBlocks_34880_34943
  have h192 := extendCertifiedSegment 34816 128 64 h128 checkBlocks_34944_35007
  have h256 := extendCertifiedSegment 34816 192 64 h192 checkBlocks_35008_35071
  have h320 := extendCertifiedSegment 34816 256 64 h256 checkBlocks_35072_35135
  have h384 := extendCertifiedSegment 34816 320 64 h320 checkBlocks_35136_35199
  have h448 := extendCertifiedSegment 34816 384 64 h384 checkBlocks_35200_35263
  have h512 := extendCertifiedSegment 34816 448 64 h448 checkBlocks_35264_35327
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_35328_35391_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35328_35391_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35328_35391 :
    ∀ i : Fin 64, indexedBlockCheck (35328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35328 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35328 0 32 h0 checkBlocks_35328_35391_part0
  have h64 := extendCertifiedSegment 35328 32 32 h32 checkBlocks_35328_35391_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35392_35455_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35392_35455_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35392_35455 :
    ∀ i : Fin 64, indexedBlockCheck (35392 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35392 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35392 0 32 h0 checkBlocks_35392_35455_part0
  have h64 := extendCertifiedSegment 35392 32 32 h32 checkBlocks_35392_35455_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35456_35519_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35456_35519_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35456_35519 :
    ∀ i : Fin 64, indexedBlockCheck (35456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35456 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35456 0 32 h0 checkBlocks_35456_35519_part0
  have h64 := extendCertifiedSegment 35456 32 32 h32 checkBlocks_35456_35519_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35520_35583_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35520_35583_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35520_35583 :
    ∀ i : Fin 64, indexedBlockCheck (35520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35520 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35520 0 32 h0 checkBlocks_35520_35583_part0
  have h64 := extendCertifiedSegment 35520 32 32 h32 checkBlocks_35520_35583_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35584_35647_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35584_35647_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35584_35647 :
    ∀ i : Fin 64, indexedBlockCheck (35584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35584 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35584 0 32 h0 checkBlocks_35584_35647_part0
  have h64 := extendCertifiedSegment 35584 32 32 h32 checkBlocks_35584_35647_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35648_35711_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35648_35711_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35648_35711 :
    ∀ i : Fin 64, indexedBlockCheck (35648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35648 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35648 0 32 h0 checkBlocks_35648_35711_part0
  have h64 := extendCertifiedSegment 35648 32 32 h32 checkBlocks_35648_35711_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35712_35775_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35712_35775_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35712_35775 :
    ∀ i : Fin 64, indexedBlockCheck (35712 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35712 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35712 0 32 h0 checkBlocks_35712_35775_part0
  have h64 := extendCertifiedSegment 35712 32 32 h32 checkBlocks_35712_35775_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35776_35839_part0 :
    ∀ i : Fin 32, indexedBlockCheck (35776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35776_35839_part1 :
    ∀ i : Fin 32, indexedBlockCheck (35808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35776_35839 :
    ∀ i : Fin 64, indexedBlockCheck (35776 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35776 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 35776 0 32 h0 checkBlocks_35776_35839_part0
  have h64 := extendCertifiedSegment 35776 32 32 h32 checkBlocks_35776_35839_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_35328_35839 :
    ∀ i : Fin 512, indexedBlockCheck (35328 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35328 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 35328 0 64 h0 checkBlocks_35328_35391
  have h128 := extendCertifiedSegment 35328 64 64 h64 checkBlocks_35392_35455
  have h192 := extendCertifiedSegment 35328 128 64 h128 checkBlocks_35456_35519
  have h256 := extendCertifiedSegment 35328 192 64 h192 checkBlocks_35520_35583
  have h320 := extendCertifiedSegment 35328 256 64 h256 checkBlocks_35584_35647
  have h384 := extendCertifiedSegment 35328 320 64 h320 checkBlocks_35648_35711
  have h448 := extendCertifiedSegment 35328 384 64 h384 checkBlocks_35712_35775
  have h512 := extendCertifiedSegment 35328 448 64 h448 checkBlocks_35776_35839
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [33792, 35840) passes the packed checker. -/
public theorem blocks_in_33792_35840 :
    ∀ i : Fin 2048, indexedBlockCheck (33792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (33792 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 33792 0 512 h0 checkBlocks_33792_34303
  have h1024 := extendCertifiedSegment 33792 512 512 h512 checkBlocks_34304_34815
  have h1536 := extendCertifiedSegment 33792 1024 512 h1024 checkBlocks_34816_35327
  have h2048 := extendCertifiedSegment 33792 1536 512 h1536 checkBlocks_35328_35839
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
