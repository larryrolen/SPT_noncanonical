/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 80896 through 82943 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_80896_80959_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80896_80959_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80896_80959 :
    ∀ i : Fin 64, indexedBlockCheck (80896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80896 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80896 0 32 h0 checkBlocks_80896_80959_part0
  have h64 := extendCertifiedSegment 80896 32 32 h32 checkBlocks_80896_80959_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80960_81023_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80960_81023_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80960_81023 :
    ∀ i : Fin 64, indexedBlockCheck (80960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80960 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80960 0 32 h0 checkBlocks_80960_81023_part0
  have h64 := extendCertifiedSegment 80960 32 32 h32 checkBlocks_80960_81023_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81024_81087_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81024_81087_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81024_81087 :
    ∀ i : Fin 64, indexedBlockCheck (81024 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81024 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81024 0 32 h0 checkBlocks_81024_81087_part0
  have h64 := extendCertifiedSegment 81024 32 32 h32 checkBlocks_81024_81087_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81088_81151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81088_81151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81088_81151 :
    ∀ i : Fin 64, indexedBlockCheck (81088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81088 0 32 h0 checkBlocks_81088_81151_part0
  have h64 := extendCertifiedSegment 81088 32 32 h32 checkBlocks_81088_81151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81152_81215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81152_81215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81152_81215 :
    ∀ i : Fin 64, indexedBlockCheck (81152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81152 0 32 h0 checkBlocks_81152_81215_part0
  have h64 := extendCertifiedSegment 81152 32 32 h32 checkBlocks_81152_81215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81216_81279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81216_81279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81216_81279 :
    ∀ i : Fin 64, indexedBlockCheck (81216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81216 0 32 h0 checkBlocks_81216_81279_part0
  have h64 := extendCertifiedSegment 81216 32 32 h32 checkBlocks_81216_81279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81280_81343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81280_81343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81280_81343 :
    ∀ i : Fin 64, indexedBlockCheck (81280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81280 0 32 h0 checkBlocks_81280_81343_part0
  have h64 := extendCertifiedSegment 81280 32 32 h32 checkBlocks_81280_81343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81344_81407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81344_81407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81344_81407 :
    ∀ i : Fin 64, indexedBlockCheck (81344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81344 0 32 h0 checkBlocks_81344_81407_part0
  have h64 := extendCertifiedSegment 81344 32 32 h32 checkBlocks_81344_81407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80896_81407 :
    ∀ i : Fin 512, indexedBlockCheck (80896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80896 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 80896 0 64 h0 checkBlocks_80896_80959
  have h128 := extendCertifiedSegment 80896 64 64 h64 checkBlocks_80960_81023
  have h192 := extendCertifiedSegment 80896 128 64 h128 checkBlocks_81024_81087
  have h256 := extendCertifiedSegment 80896 192 64 h192 checkBlocks_81088_81151
  have h320 := extendCertifiedSegment 80896 256 64 h256 checkBlocks_81152_81215
  have h384 := extendCertifiedSegment 80896 320 64 h320 checkBlocks_81216_81279
  have h448 := extendCertifiedSegment 80896 384 64 h384 checkBlocks_81280_81343
  have h512 := extendCertifiedSegment 80896 448 64 h448 checkBlocks_81344_81407
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_81408_81471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81408_81471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81408_81471 :
    ∀ i : Fin 64, indexedBlockCheck (81408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81408 0 32 h0 checkBlocks_81408_81471_part0
  have h64 := extendCertifiedSegment 81408 32 32 h32 checkBlocks_81408_81471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81472_81535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81472_81535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81472_81535 :
    ∀ i : Fin 64, indexedBlockCheck (81472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81472 0 32 h0 checkBlocks_81472_81535_part0
  have h64 := extendCertifiedSegment 81472 32 32 h32 checkBlocks_81472_81535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81536_81599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81536_81599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81536_81599 :
    ∀ i : Fin 64, indexedBlockCheck (81536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81536 0 32 h0 checkBlocks_81536_81599_part0
  have h64 := extendCertifiedSegment 81536 32 32 h32 checkBlocks_81536_81599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81600_81663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81600_81663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81600_81663 :
    ∀ i : Fin 64, indexedBlockCheck (81600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81600 0 32 h0 checkBlocks_81600_81663_part0
  have h64 := extendCertifiedSegment 81600 32 32 h32 checkBlocks_81600_81663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81664_81727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81664_81727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81664_81727 :
    ∀ i : Fin 64, indexedBlockCheck (81664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81664 0 32 h0 checkBlocks_81664_81727_part0
  have h64 := extendCertifiedSegment 81664 32 32 h32 checkBlocks_81664_81727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81728_81791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81728_81791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81728_81791 :
    ∀ i : Fin 64, indexedBlockCheck (81728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81728 0 32 h0 checkBlocks_81728_81791_part0
  have h64 := extendCertifiedSegment 81728 32 32 h32 checkBlocks_81728_81791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81792_81855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81792_81855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81792_81855 :
    ∀ i : Fin 64, indexedBlockCheck (81792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81792 0 32 h0 checkBlocks_81792_81855_part0
  have h64 := extendCertifiedSegment 81792 32 32 h32 checkBlocks_81792_81855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81856_81919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81856_81919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81856_81919 :
    ∀ i : Fin 64, indexedBlockCheck (81856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81856 0 32 h0 checkBlocks_81856_81919_part0
  have h64 := extendCertifiedSegment 81856 32 32 h32 checkBlocks_81856_81919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81408_81919 :
    ∀ i : Fin 512, indexedBlockCheck (81408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81408 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 81408 0 64 h0 checkBlocks_81408_81471
  have h128 := extendCertifiedSegment 81408 64 64 h64 checkBlocks_81472_81535
  have h192 := extendCertifiedSegment 81408 128 64 h128 checkBlocks_81536_81599
  have h256 := extendCertifiedSegment 81408 192 64 h192 checkBlocks_81600_81663
  have h320 := extendCertifiedSegment 81408 256 64 h256 checkBlocks_81664_81727
  have h384 := extendCertifiedSegment 81408 320 64 h320 checkBlocks_81728_81791
  have h448 := extendCertifiedSegment 81408 384 64 h384 checkBlocks_81792_81855
  have h512 := extendCertifiedSegment 81408 448 64 h448 checkBlocks_81856_81919
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_81920_81983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81920_81983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (81952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81920_81983 :
    ∀ i : Fin 64, indexedBlockCheck (81920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81920 0 32 h0 checkBlocks_81920_81983_part0
  have h64 := extendCertifiedSegment 81920 32 32 h32 checkBlocks_81920_81983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81984_82047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (81984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81984_82047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_81984_82047 :
    ∀ i : Fin 64, indexedBlockCheck (81984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 81984 0 32 h0 checkBlocks_81984_82047_part0
  have h64 := extendCertifiedSegment 81984 32 32 h32 checkBlocks_81984_82047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82048_82111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82048_82111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82048_82111 :
    ∀ i : Fin 64, indexedBlockCheck (82048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82048 0 32 h0 checkBlocks_82048_82111_part0
  have h64 := extendCertifiedSegment 82048 32 32 h32 checkBlocks_82048_82111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82112_82175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82112_82175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82112_82175 :
    ∀ i : Fin 64, indexedBlockCheck (82112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82112 0 32 h0 checkBlocks_82112_82175_part0
  have h64 := extendCertifiedSegment 82112 32 32 h32 checkBlocks_82112_82175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82176_82239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82176_82239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82176_82239 :
    ∀ i : Fin 64, indexedBlockCheck (82176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82176 0 32 h0 checkBlocks_82176_82239_part0
  have h64 := extendCertifiedSegment 82176 32 32 h32 checkBlocks_82176_82239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82240_82303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82240_82303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82240_82303 :
    ∀ i : Fin 64, indexedBlockCheck (82240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82240 0 32 h0 checkBlocks_82240_82303_part0
  have h64 := extendCertifiedSegment 82240 32 32 h32 checkBlocks_82240_82303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82304_82367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82304_82367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82304_82367 :
    ∀ i : Fin 64, indexedBlockCheck (82304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82304 0 32 h0 checkBlocks_82304_82367_part0
  have h64 := extendCertifiedSegment 82304 32 32 h32 checkBlocks_82304_82367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82368_82431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82368_82431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82368_82431 :
    ∀ i : Fin 64, indexedBlockCheck (82368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82368 0 32 h0 checkBlocks_82368_82431_part0
  have h64 := extendCertifiedSegment 82368 32 32 h32 checkBlocks_82368_82431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_81920_82431 :
    ∀ i : Fin 512, indexedBlockCheck (81920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (81920 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 81920 0 64 h0 checkBlocks_81920_81983
  have h128 := extendCertifiedSegment 81920 64 64 h64 checkBlocks_81984_82047
  have h192 := extendCertifiedSegment 81920 128 64 h128 checkBlocks_82048_82111
  have h256 := extendCertifiedSegment 81920 192 64 h192 checkBlocks_82112_82175
  have h320 := extendCertifiedSegment 81920 256 64 h256 checkBlocks_82176_82239
  have h384 := extendCertifiedSegment 81920 320 64 h320 checkBlocks_82240_82303
  have h448 := extendCertifiedSegment 81920 384 64 h384 checkBlocks_82304_82367
  have h512 := extendCertifiedSegment 81920 448 64 h448 checkBlocks_82368_82431
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_82432_82495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82432_82495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82432_82495 :
    ∀ i : Fin 64, indexedBlockCheck (82432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82432 0 32 h0 checkBlocks_82432_82495_part0
  have h64 := extendCertifiedSegment 82432 32 32 h32 checkBlocks_82432_82495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82496_82559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82496_82559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82496_82559 :
    ∀ i : Fin 64, indexedBlockCheck (82496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82496 0 32 h0 checkBlocks_82496_82559_part0
  have h64 := extendCertifiedSegment 82496 32 32 h32 checkBlocks_82496_82559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82560_82623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82560_82623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82560_82623 :
    ∀ i : Fin 64, indexedBlockCheck (82560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82560 0 32 h0 checkBlocks_82560_82623_part0
  have h64 := extendCertifiedSegment 82560 32 32 h32 checkBlocks_82560_82623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82624_82687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82624_82687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82624_82687 :
    ∀ i : Fin 64, indexedBlockCheck (82624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82624 0 32 h0 checkBlocks_82624_82687_part0
  have h64 := extendCertifiedSegment 82624 32 32 h32 checkBlocks_82624_82687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82688_82751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82688_82751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82688_82751 :
    ∀ i : Fin 64, indexedBlockCheck (82688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82688 0 32 h0 checkBlocks_82688_82751_part0
  have h64 := extendCertifiedSegment 82688 32 32 h32 checkBlocks_82688_82751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82752_82815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82752_82815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82752_82815 :
    ∀ i : Fin 64, indexedBlockCheck (82752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82752 0 32 h0 checkBlocks_82752_82815_part0
  have h64 := extendCertifiedSegment 82752 32 32 h32 checkBlocks_82752_82815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82816_82879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82816_82879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82816_82879 :
    ∀ i : Fin 64, indexedBlockCheck (82816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82816 0 32 h0 checkBlocks_82816_82879_part0
  have h64 := extendCertifiedSegment 82816 32 32 h32 checkBlocks_82816_82879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82880_82943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (82880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82880_82943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (82912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82880_82943 :
    ∀ i : Fin 64, indexedBlockCheck (82880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 82880 0 32 h0 checkBlocks_82880_82943_part0
  have h64 := extendCertifiedSegment 82880 32 32 h32 checkBlocks_82880_82943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_82432_82943 :
    ∀ i : Fin 512, indexedBlockCheck (82432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82432 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 82432 0 64 h0 checkBlocks_82432_82495
  have h128 := extendCertifiedSegment 82432 64 64 h64 checkBlocks_82496_82559
  have h192 := extendCertifiedSegment 82432 128 64 h128 checkBlocks_82560_82623
  have h256 := extendCertifiedSegment 82432 192 64 h192 checkBlocks_82624_82687
  have h320 := extendCertifiedSegment 82432 256 64 h256 checkBlocks_82688_82751
  have h384 := extendCertifiedSegment 82432 320 64 h320 checkBlocks_82752_82815
  have h448 := extendCertifiedSegment 82432 384 64 h384 checkBlocks_82816_82879
  have h512 := extendCertifiedSegment 82432 448 64 h448 checkBlocks_82880_82943
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [80896, 82944) passes the packed checker. -/
public theorem blocks_in_80896_82944 :
    ∀ i : Fin 2048, indexedBlockCheck (80896 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80896 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 80896 0 512 h0 checkBlocks_80896_81407
  have h1024 := extendCertifiedSegment 80896 512 512 h512 checkBlocks_81408_81919
  have h1536 := extendCertifiedSegment 80896 1024 512 h1024 checkBlocks_81920_82431
  have h2048 := extendCertifiedSegment 80896 1536 512 h1536 checkBlocks_82432_82943
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
