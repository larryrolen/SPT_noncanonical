/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 9216 through 11263 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_9216_9279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9216_9279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9216_9279 :
    ∀ i : Fin 64, indexedBlockCheck (9216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9216 0 32 h0 checkBlocks_9216_9279_part0
  have h64 := extendCertifiedSegment 9216 32 32 h32 checkBlocks_9216_9279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9280_9343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9280_9343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9280_9343 :
    ∀ i : Fin 64, indexedBlockCheck (9280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9280 0 32 h0 checkBlocks_9280_9343_part0
  have h64 := extendCertifiedSegment 9280 32 32 h32 checkBlocks_9280_9343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9344_9407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9344_9407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9344_9407 :
    ∀ i : Fin 64, indexedBlockCheck (9344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9344 0 32 h0 checkBlocks_9344_9407_part0
  have h64 := extendCertifiedSegment 9344 32 32 h32 checkBlocks_9344_9407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9408_9471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9408_9471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9408_9471 :
    ∀ i : Fin 64, indexedBlockCheck (9408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9408 0 32 h0 checkBlocks_9408_9471_part0
  have h64 := extendCertifiedSegment 9408 32 32 h32 checkBlocks_9408_9471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9472_9535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9472_9535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9472_9535 :
    ∀ i : Fin 64, indexedBlockCheck (9472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9472 0 32 h0 checkBlocks_9472_9535_part0
  have h64 := extendCertifiedSegment 9472 32 32 h32 checkBlocks_9472_9535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9536_9599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9536_9599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9536_9599 :
    ∀ i : Fin 64, indexedBlockCheck (9536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9536 0 32 h0 checkBlocks_9536_9599_part0
  have h64 := extendCertifiedSegment 9536 32 32 h32 checkBlocks_9536_9599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9600_9663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9600_9663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9600_9663 :
    ∀ i : Fin 64, indexedBlockCheck (9600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9600 0 32 h0 checkBlocks_9600_9663_part0
  have h64 := extendCertifiedSegment 9600 32 32 h32 checkBlocks_9600_9663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9664_9727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9664_9727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9664_9727 :
    ∀ i : Fin 64, indexedBlockCheck (9664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9664 0 32 h0 checkBlocks_9664_9727_part0
  have h64 := extendCertifiedSegment 9664 32 32 h32 checkBlocks_9664_9727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9216_9727 :
    ∀ i : Fin 512, indexedBlockCheck (9216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9216 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 9216 0 64 h0 checkBlocks_9216_9279
  have h128 := extendCertifiedSegment 9216 64 64 h64 checkBlocks_9280_9343
  have h192 := extendCertifiedSegment 9216 128 64 h128 checkBlocks_9344_9407
  have h256 := extendCertifiedSegment 9216 192 64 h192 checkBlocks_9408_9471
  have h320 := extendCertifiedSegment 9216 256 64 h256 checkBlocks_9472_9535
  have h384 := extendCertifiedSegment 9216 320 64 h320 checkBlocks_9536_9599
  have h448 := extendCertifiedSegment 9216 384 64 h384 checkBlocks_9600_9663
  have h512 := extendCertifiedSegment 9216 448 64 h448 checkBlocks_9664_9727
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_9728_9791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9728_9791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9728_9791 :
    ∀ i : Fin 64, indexedBlockCheck (9728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9728 0 32 h0 checkBlocks_9728_9791_part0
  have h64 := extendCertifiedSegment 9728 32 32 h32 checkBlocks_9728_9791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9792_9855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9792_9855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9792_9855 :
    ∀ i : Fin 64, indexedBlockCheck (9792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9792 0 32 h0 checkBlocks_9792_9855_part0
  have h64 := extendCertifiedSegment 9792 32 32 h32 checkBlocks_9792_9855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9856_9919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9856_9919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9856_9919 :
    ∀ i : Fin 64, indexedBlockCheck (9856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9856 0 32 h0 checkBlocks_9856_9919_part0
  have h64 := extendCertifiedSegment 9856 32 32 h32 checkBlocks_9856_9919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9920_9983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9920_9983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (9952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9920_9983 :
    ∀ i : Fin 64, indexedBlockCheck (9920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9920 0 32 h0 checkBlocks_9920_9983_part0
  have h64 := extendCertifiedSegment 9920 32 32 h32 checkBlocks_9920_9983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9984_10047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (9984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9984_10047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_9984_10047 :
    ∀ i : Fin 64, indexedBlockCheck (9984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 9984 0 32 h0 checkBlocks_9984_10047_part0
  have h64 := extendCertifiedSegment 9984 32 32 h32 checkBlocks_9984_10047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10048_10111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10048_10111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10048_10111 :
    ∀ i : Fin 64, indexedBlockCheck (10048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10048 0 32 h0 checkBlocks_10048_10111_part0
  have h64 := extendCertifiedSegment 10048 32 32 h32 checkBlocks_10048_10111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10112_10175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10112_10175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10112_10175 :
    ∀ i : Fin 64, indexedBlockCheck (10112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10112 0 32 h0 checkBlocks_10112_10175_part0
  have h64 := extendCertifiedSegment 10112 32 32 h32 checkBlocks_10112_10175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10176_10239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10176_10239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10176_10239 :
    ∀ i : Fin 64, indexedBlockCheck (10176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10176 0 32 h0 checkBlocks_10176_10239_part0
  have h64 := extendCertifiedSegment 10176 32 32 h32 checkBlocks_10176_10239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_9728_10239 :
    ∀ i : Fin 512, indexedBlockCheck (9728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9728 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 9728 0 64 h0 checkBlocks_9728_9791
  have h128 := extendCertifiedSegment 9728 64 64 h64 checkBlocks_9792_9855
  have h192 := extendCertifiedSegment 9728 128 64 h128 checkBlocks_9856_9919
  have h256 := extendCertifiedSegment 9728 192 64 h192 checkBlocks_9920_9983
  have h320 := extendCertifiedSegment 9728 256 64 h256 checkBlocks_9984_10047
  have h384 := extendCertifiedSegment 9728 320 64 h320 checkBlocks_10048_10111
  have h448 := extendCertifiedSegment 9728 384 64 h384 checkBlocks_10112_10175
  have h512 := extendCertifiedSegment 9728 448 64 h448 checkBlocks_10176_10239
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_10240_10303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10240_10303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10240_10303 :
    ∀ i : Fin 64, indexedBlockCheck (10240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10240 0 32 h0 checkBlocks_10240_10303_part0
  have h64 := extendCertifiedSegment 10240 32 32 h32 checkBlocks_10240_10303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10304_10367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10304_10367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10304_10367 :
    ∀ i : Fin 64, indexedBlockCheck (10304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10304 0 32 h0 checkBlocks_10304_10367_part0
  have h64 := extendCertifiedSegment 10304 32 32 h32 checkBlocks_10304_10367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10368_10431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10368_10431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10368_10431 :
    ∀ i : Fin 64, indexedBlockCheck (10368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10368 0 32 h0 checkBlocks_10368_10431_part0
  have h64 := extendCertifiedSegment 10368 32 32 h32 checkBlocks_10368_10431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10432_10495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10432_10495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10432_10495 :
    ∀ i : Fin 64, indexedBlockCheck (10432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10432 0 32 h0 checkBlocks_10432_10495_part0
  have h64 := extendCertifiedSegment 10432 32 32 h32 checkBlocks_10432_10495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10496_10559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10496_10559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10496_10559 :
    ∀ i : Fin 64, indexedBlockCheck (10496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10496 0 32 h0 checkBlocks_10496_10559_part0
  have h64 := extendCertifiedSegment 10496 32 32 h32 checkBlocks_10496_10559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10560_10623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10560_10623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10560_10623 :
    ∀ i : Fin 64, indexedBlockCheck (10560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10560 0 32 h0 checkBlocks_10560_10623_part0
  have h64 := extendCertifiedSegment 10560 32 32 h32 checkBlocks_10560_10623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10624_10687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10624_10687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10624_10687 :
    ∀ i : Fin 64, indexedBlockCheck (10624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10624 0 32 h0 checkBlocks_10624_10687_part0
  have h64 := extendCertifiedSegment 10624 32 32 h32 checkBlocks_10624_10687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10688_10751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10688_10751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10688_10751 :
    ∀ i : Fin 64, indexedBlockCheck (10688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10688 0 32 h0 checkBlocks_10688_10751_part0
  have h64 := extendCertifiedSegment 10688 32 32 h32 checkBlocks_10688_10751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10240_10751 :
    ∀ i : Fin 512, indexedBlockCheck (10240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10240 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 10240 0 64 h0 checkBlocks_10240_10303
  have h128 := extendCertifiedSegment 10240 64 64 h64 checkBlocks_10304_10367
  have h192 := extendCertifiedSegment 10240 128 64 h128 checkBlocks_10368_10431
  have h256 := extendCertifiedSegment 10240 192 64 h192 checkBlocks_10432_10495
  have h320 := extendCertifiedSegment 10240 256 64 h256 checkBlocks_10496_10559
  have h384 := extendCertifiedSegment 10240 320 64 h320 checkBlocks_10560_10623
  have h448 := extendCertifiedSegment 10240 384 64 h384 checkBlocks_10624_10687
  have h512 := extendCertifiedSegment 10240 448 64 h448 checkBlocks_10688_10751
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_10752_10815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10752_10815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10752_10815 :
    ∀ i : Fin 64, indexedBlockCheck (10752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10752 0 32 h0 checkBlocks_10752_10815_part0
  have h64 := extendCertifiedSegment 10752 32 32 h32 checkBlocks_10752_10815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10816_10879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10816_10879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10816_10879 :
    ∀ i : Fin 64, indexedBlockCheck (10816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10816 0 32 h0 checkBlocks_10816_10879_part0
  have h64 := extendCertifiedSegment 10816 32 32 h32 checkBlocks_10816_10879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10880_10943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10880_10943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10880_10943 :
    ∀ i : Fin 64, indexedBlockCheck (10880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10880 0 32 h0 checkBlocks_10880_10943_part0
  have h64 := extendCertifiedSegment 10880 32 32 h32 checkBlocks_10880_10943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10944_11007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (10944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10944_11007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (10976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_10944_11007 :
    ∀ i : Fin 64, indexedBlockCheck (10944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 10944 0 32 h0 checkBlocks_10944_11007_part0
  have h64 := extendCertifiedSegment 10944 32 32 h32 checkBlocks_10944_11007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11008_11071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11008_11071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11008_11071 :
    ∀ i : Fin 64, indexedBlockCheck (11008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11008 0 32 h0 checkBlocks_11008_11071_part0
  have h64 := extendCertifiedSegment 11008 32 32 h32 checkBlocks_11008_11071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11072_11135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11072_11135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11072_11135 :
    ∀ i : Fin 64, indexedBlockCheck (11072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11072 0 32 h0 checkBlocks_11072_11135_part0
  have h64 := extendCertifiedSegment 11072 32 32 h32 checkBlocks_11072_11135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11136_11199_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11136_11199_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11136_11199 :
    ∀ i : Fin 64, indexedBlockCheck (11136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11136 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11136 0 32 h0 checkBlocks_11136_11199_part0
  have h64 := extendCertifiedSegment 11136 32 32 h32 checkBlocks_11136_11199_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_11200_11263_part0 :
    ∀ i : Fin 32, indexedBlockCheck (11200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11200_11263_part1 :
    ∀ i : Fin 32, indexedBlockCheck (11232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_11200_11263 :
    ∀ i : Fin 64, indexedBlockCheck (11200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (11200 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 11200 0 32 h0 checkBlocks_11200_11263_part0
  have h64 := extendCertifiedSegment 11200 32 32 h32 checkBlocks_11200_11263_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_10752_11263 :
    ∀ i : Fin 512, indexedBlockCheck (10752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (10752 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 10752 0 64 h0 checkBlocks_10752_10815
  have h128 := extendCertifiedSegment 10752 64 64 h64 checkBlocks_10816_10879
  have h192 := extendCertifiedSegment 10752 128 64 h128 checkBlocks_10880_10943
  have h256 := extendCertifiedSegment 10752 192 64 h192 checkBlocks_10944_11007
  have h320 := extendCertifiedSegment 10752 256 64 h256 checkBlocks_11008_11071
  have h384 := extendCertifiedSegment 10752 320 64 h320 checkBlocks_11072_11135
  have h448 := extendCertifiedSegment 10752 384 64 h384 checkBlocks_11136_11199
  have h512 := extendCertifiedSegment 10752 448 64 h448 checkBlocks_11200_11263
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [9216, 11264) passes the packed checker. -/
public theorem blocks_in_9216_11264 :
    ∀ i : Fin 2048, indexedBlockCheck (9216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (9216 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 9216 0 512 h0 checkBlocks_9216_9727
  have h1024 := extendCertifiedSegment 9216 512 512 h512 checkBlocks_9728_10239
  have h1536 := extendCertifiedSegment 9216 1024 512 h1024 checkBlocks_10240_10751
  have h2048 := extendCertifiedSegment 9216 1536 512 h1536 checkBlocks_10752_11263
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
