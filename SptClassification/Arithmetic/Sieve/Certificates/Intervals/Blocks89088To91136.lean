/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 89088 through 91135 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_89088_89151_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89088_89151_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89088_89151 :
    ∀ i : Fin 64, indexedBlockCheck (89088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89088 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89088 0 32 h0 checkBlocks_89088_89151_part0
  have h64 := extendCertifiedSegment 89088 32 32 h32 checkBlocks_89088_89151_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89152_89215_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89152_89215_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89152_89215 :
    ∀ i : Fin 64, indexedBlockCheck (89152 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89152 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89152 0 32 h0 checkBlocks_89152_89215_part0
  have h64 := extendCertifiedSegment 89152 32 32 h32 checkBlocks_89152_89215_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89216_89279_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89216_89279_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89216_89279 :
    ∀ i : Fin 64, indexedBlockCheck (89216 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89216 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89216 0 32 h0 checkBlocks_89216_89279_part0
  have h64 := extendCertifiedSegment 89216 32 32 h32 checkBlocks_89216_89279_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89280_89343_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89280_89343_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89280_89343 :
    ∀ i : Fin 64, indexedBlockCheck (89280 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89280 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89280 0 32 h0 checkBlocks_89280_89343_part0
  have h64 := extendCertifiedSegment 89280 32 32 h32 checkBlocks_89280_89343_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89344_89407_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89344_89407_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89344_89407 :
    ∀ i : Fin 64, indexedBlockCheck (89344 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89344 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89344 0 32 h0 checkBlocks_89344_89407_part0
  have h64 := extendCertifiedSegment 89344 32 32 h32 checkBlocks_89344_89407_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89408_89471_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89408_89471_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89408_89471 :
    ∀ i : Fin 64, indexedBlockCheck (89408 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89408 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89408 0 32 h0 checkBlocks_89408_89471_part0
  have h64 := extendCertifiedSegment 89408 32 32 h32 checkBlocks_89408_89471_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89472_89535_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89472_89535_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89472_89535 :
    ∀ i : Fin 64, indexedBlockCheck (89472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89472 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89472 0 32 h0 checkBlocks_89472_89535_part0
  have h64 := extendCertifiedSegment 89472 32 32 h32 checkBlocks_89472_89535_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89536_89599_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89536_89599_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89536_89599 :
    ∀ i : Fin 64, indexedBlockCheck (89536 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89536 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89536 0 32 h0 checkBlocks_89536_89599_part0
  have h64 := extendCertifiedSegment 89536 32 32 h32 checkBlocks_89536_89599_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89088_89599 :
    ∀ i : Fin 512, indexedBlockCheck (89088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89088 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 89088 0 64 h0 checkBlocks_89088_89151
  have h128 := extendCertifiedSegment 89088 64 64 h64 checkBlocks_89152_89215
  have h192 := extendCertifiedSegment 89088 128 64 h128 checkBlocks_89216_89279
  have h256 := extendCertifiedSegment 89088 192 64 h192 checkBlocks_89280_89343
  have h320 := extendCertifiedSegment 89088 256 64 h256 checkBlocks_89344_89407
  have h384 := extendCertifiedSegment 89088 320 64 h320 checkBlocks_89408_89471
  have h448 := extendCertifiedSegment 89088 384 64 h384 checkBlocks_89472_89535
  have h512 := extendCertifiedSegment 89088 448 64 h448 checkBlocks_89536_89599
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_89600_89663_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89600_89663_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89600_89663 :
    ∀ i : Fin 64, indexedBlockCheck (89600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89600 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89600 0 32 h0 checkBlocks_89600_89663_part0
  have h64 := extendCertifiedSegment 89600 32 32 h32 checkBlocks_89600_89663_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89664_89727_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89664_89727_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89664_89727 :
    ∀ i : Fin 64, indexedBlockCheck (89664 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89664 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89664 0 32 h0 checkBlocks_89664_89727_part0
  have h64 := extendCertifiedSegment 89664 32 32 h32 checkBlocks_89664_89727_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89728_89791_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89728_89791_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89728_89791 :
    ∀ i : Fin 64, indexedBlockCheck (89728 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89728 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89728 0 32 h0 checkBlocks_89728_89791_part0
  have h64 := extendCertifiedSegment 89728 32 32 h32 checkBlocks_89728_89791_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89792_89855_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89792_89855_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89792_89855 :
    ∀ i : Fin 64, indexedBlockCheck (89792 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89792 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89792 0 32 h0 checkBlocks_89792_89855_part0
  have h64 := extendCertifiedSegment 89792 32 32 h32 checkBlocks_89792_89855_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89856_89919_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89856_89919_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89856_89919 :
    ∀ i : Fin 64, indexedBlockCheck (89856 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89856 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89856 0 32 h0 checkBlocks_89856_89919_part0
  have h64 := extendCertifiedSegment 89856 32 32 h32 checkBlocks_89856_89919_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89920_89983_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89920_89983_part1 :
    ∀ i : Fin 32, indexedBlockCheck (89952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89920_89983 :
    ∀ i : Fin 64, indexedBlockCheck (89920 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89920 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89920 0 32 h0 checkBlocks_89920_89983_part0
  have h64 := extendCertifiedSegment 89920 32 32 h32 checkBlocks_89920_89983_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89984_90047_part0 :
    ∀ i : Fin 32, indexedBlockCheck (89984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89984_90047_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_89984_90047 :
    ∀ i : Fin 64, indexedBlockCheck (89984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89984 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 89984 0 32 h0 checkBlocks_89984_90047_part0
  have h64 := extendCertifiedSegment 89984 32 32 h32 checkBlocks_89984_90047_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90048_90111_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90048_90111_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90048_90111 :
    ∀ i : Fin 64, indexedBlockCheck (90048 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90048 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90048 0 32 h0 checkBlocks_90048_90111_part0
  have h64 := extendCertifiedSegment 90048 32 32 h32 checkBlocks_90048_90111_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_89600_90111 :
    ∀ i : Fin 512, indexedBlockCheck (89600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89600 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 89600 0 64 h0 checkBlocks_89600_89663
  have h128 := extendCertifiedSegment 89600 64 64 h64 checkBlocks_89664_89727
  have h192 := extendCertifiedSegment 89600 128 64 h128 checkBlocks_89728_89791
  have h256 := extendCertifiedSegment 89600 192 64 h192 checkBlocks_89792_89855
  have h320 := extendCertifiedSegment 89600 256 64 h256 checkBlocks_89856_89919
  have h384 := extendCertifiedSegment 89600 320 64 h320 checkBlocks_89920_89983
  have h448 := extendCertifiedSegment 89600 384 64 h384 checkBlocks_89984_90047
  have h512 := extendCertifiedSegment 89600 448 64 h448 checkBlocks_90048_90111
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_90112_90175_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90112_90175_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90112_90175 :
    ∀ i : Fin 64, indexedBlockCheck (90112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90112 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90112 0 32 h0 checkBlocks_90112_90175_part0
  have h64 := extendCertifiedSegment 90112 32 32 h32 checkBlocks_90112_90175_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90176_90239_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90176_90239_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90176_90239 :
    ∀ i : Fin 64, indexedBlockCheck (90176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90176 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90176 0 32 h0 checkBlocks_90176_90239_part0
  have h64 := extendCertifiedSegment 90176 32 32 h32 checkBlocks_90176_90239_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90240_90303_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90240_90303_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90240_90303 :
    ∀ i : Fin 64, indexedBlockCheck (90240 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90240 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90240 0 32 h0 checkBlocks_90240_90303_part0
  have h64 := extendCertifiedSegment 90240 32 32 h32 checkBlocks_90240_90303_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90304_90367_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90304_90367_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90304_90367 :
    ∀ i : Fin 64, indexedBlockCheck (90304 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90304 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90304 0 32 h0 checkBlocks_90304_90367_part0
  have h64 := extendCertifiedSegment 90304 32 32 h32 checkBlocks_90304_90367_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90368_90431_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90368_90431_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90368_90431 :
    ∀ i : Fin 64, indexedBlockCheck (90368 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90368 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90368 0 32 h0 checkBlocks_90368_90431_part0
  have h64 := extendCertifiedSegment 90368 32 32 h32 checkBlocks_90368_90431_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90432_90495_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90432_90495_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90432_90495 :
    ∀ i : Fin 64, indexedBlockCheck (90432 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90432 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90432 0 32 h0 checkBlocks_90432_90495_part0
  have h64 := extendCertifiedSegment 90432 32 32 h32 checkBlocks_90432_90495_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90496_90559_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90496_90559_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90496_90559 :
    ∀ i : Fin 64, indexedBlockCheck (90496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90496 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90496 0 32 h0 checkBlocks_90496_90559_part0
  have h64 := extendCertifiedSegment 90496 32 32 h32 checkBlocks_90496_90559_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90560_90623_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90560_90623_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90560_90623 :
    ∀ i : Fin 64, indexedBlockCheck (90560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90560 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90560 0 32 h0 checkBlocks_90560_90623_part0
  have h64 := extendCertifiedSegment 90560 32 32 h32 checkBlocks_90560_90623_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90112_90623 :
    ∀ i : Fin 512, indexedBlockCheck (90112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90112 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 90112 0 64 h0 checkBlocks_90112_90175
  have h128 := extendCertifiedSegment 90112 64 64 h64 checkBlocks_90176_90239
  have h192 := extendCertifiedSegment 90112 128 64 h128 checkBlocks_90240_90303
  have h256 := extendCertifiedSegment 90112 192 64 h192 checkBlocks_90304_90367
  have h320 := extendCertifiedSegment 90112 256 64 h256 checkBlocks_90368_90431
  have h384 := extendCertifiedSegment 90112 320 64 h320 checkBlocks_90432_90495
  have h448 := extendCertifiedSegment 90112 384 64 h384 checkBlocks_90496_90559
  have h512 := extendCertifiedSegment 90112 448 64 h448 checkBlocks_90560_90623
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_90624_90687_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90624_90687_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90624_90687 :
    ∀ i : Fin 64, indexedBlockCheck (90624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90624 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90624 0 32 h0 checkBlocks_90624_90687_part0
  have h64 := extendCertifiedSegment 90624 32 32 h32 checkBlocks_90624_90687_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90688_90751_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90688_90751_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90688_90751 :
    ∀ i : Fin 64, indexedBlockCheck (90688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90688 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90688 0 32 h0 checkBlocks_90688_90751_part0
  have h64 := extendCertifiedSegment 90688 32 32 h32 checkBlocks_90688_90751_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90752_90815_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90752_90815_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90752_90815 :
    ∀ i : Fin 64, indexedBlockCheck (90752 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90752 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90752 0 32 h0 checkBlocks_90752_90815_part0
  have h64 := extendCertifiedSegment 90752 32 32 h32 checkBlocks_90752_90815_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90816_90879_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90816_90879_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90816_90879 :
    ∀ i : Fin 64, indexedBlockCheck (90816 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90816 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90816 0 32 h0 checkBlocks_90816_90879_part0
  have h64 := extendCertifiedSegment 90816 32 32 h32 checkBlocks_90816_90879_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90880_90943_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90880_90943_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90880_90943 :
    ∀ i : Fin 64, indexedBlockCheck (90880 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90880 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90880 0 32 h0 checkBlocks_90880_90943_part0
  have h64 := extendCertifiedSegment 90880 32 32 h32 checkBlocks_90880_90943_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90944_91007_part0 :
    ∀ i : Fin 32, indexedBlockCheck (90944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90944_91007_part1 :
    ∀ i : Fin 32, indexedBlockCheck (90976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_90944_91007 :
    ∀ i : Fin 64, indexedBlockCheck (90944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90944 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 90944 0 32 h0 checkBlocks_90944_91007_part0
  have h64 := extendCertifiedSegment 90944 32 32 h32 checkBlocks_90944_91007_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_91008_91071_part0 :
    ∀ i : Fin 32, indexedBlockCheck (91008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91008_91071_part1 :
    ∀ i : Fin 32, indexedBlockCheck (91040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91008_91071 :
    ∀ i : Fin 64, indexedBlockCheck (91008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (91008 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 91008 0 32 h0 checkBlocks_91008_91071_part0
  have h64 := extendCertifiedSegment 91008 32 32 h32 checkBlocks_91008_91071_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_91072_91135_part0 :
    ∀ i : Fin 32, indexedBlockCheck (91072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91072_91135_part1 :
    ∀ i : Fin 32, indexedBlockCheck (91104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_91072_91135 :
    ∀ i : Fin 64, indexedBlockCheck (91072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (91072 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 91072 0 32 h0 checkBlocks_91072_91135_part0
  have h64 := extendCertifiedSegment 91072 32 32 h32 checkBlocks_91072_91135_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_90624_91135 :
    ∀ i : Fin 512, indexedBlockCheck (90624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (90624 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 90624 0 64 h0 checkBlocks_90624_90687
  have h128 := extendCertifiedSegment 90624 64 64 h64 checkBlocks_90688_90751
  have h192 := extendCertifiedSegment 90624 128 64 h128 checkBlocks_90752_90815
  have h256 := extendCertifiedSegment 90624 192 64 h192 checkBlocks_90816_90879
  have h320 := extendCertifiedSegment 90624 256 64 h256 checkBlocks_90880_90943
  have h384 := extendCertifiedSegment 90624 320 64 h320 checkBlocks_90944_91007
  have h448 := extendCertifiedSegment 90624 384 64 h384 checkBlocks_91008_91071
  have h512 := extendCertifiedSegment 90624 448 64 h448 checkBlocks_91072_91135
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [89088, 91136) passes the packed checker. -/
public theorem blocks_in_89088_91136 :
    ∀ i : Fin 2048, indexedBlockCheck (89088 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (89088 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 89088 0 512 h0 checkBlocks_89088_89599
  have h1024 := extendCertifiedSegment 89088 512 512 h512 checkBlocks_89600_90111
  have h1536 := extendCertifiedSegment 89088 1024 512 h1024 checkBlocks_90112_90623
  have h2048 := extendCertifiedSegment 89088 1536 512 h1536 checkBlocks_90624_91135
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
