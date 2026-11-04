/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 44032 through 46079 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_44032_44095_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44032_44095_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44032_44095 :
    ∀ i : Fin 64, indexedBlockCheck (44032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44032 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44032 0 32 h0 checkBlocks_44032_44095_part0
  have h64 := extendCertifiedSegment 44032 32 32 h32 checkBlocks_44032_44095_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44096_44159_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44096_44159_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44096_44159 :
    ∀ i : Fin 64, indexedBlockCheck (44096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44096 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44096 0 32 h0 checkBlocks_44096_44159_part0
  have h64 := extendCertifiedSegment 44096 32 32 h32 checkBlocks_44096_44159_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44160_44223_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44160_44223_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44160_44223 :
    ∀ i : Fin 64, indexedBlockCheck (44160 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44160 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44160 0 32 h0 checkBlocks_44160_44223_part0
  have h64 := extendCertifiedSegment 44160 32 32 h32 checkBlocks_44160_44223_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44224_44287_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44224_44287_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44224_44287 :
    ∀ i : Fin 64, indexedBlockCheck (44224 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44224 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44224 0 32 h0 checkBlocks_44224_44287_part0
  have h64 := extendCertifiedSegment 44224 32 32 h32 checkBlocks_44224_44287_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44288_44351_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44288_44351_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44288_44351 :
    ∀ i : Fin 64, indexedBlockCheck (44288 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44288 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44288 0 32 h0 checkBlocks_44288_44351_part0
  have h64 := extendCertifiedSegment 44288 32 32 h32 checkBlocks_44288_44351_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44352_44415_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44352_44415_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44352_44415 :
    ∀ i : Fin 64, indexedBlockCheck (44352 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44352 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44352 0 32 h0 checkBlocks_44352_44415_part0
  have h64 := extendCertifiedSegment 44352 32 32 h32 checkBlocks_44352_44415_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44416_44479_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44416_44479_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44416_44479 :
    ∀ i : Fin 64, indexedBlockCheck (44416 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44416 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44416 0 32 h0 checkBlocks_44416_44479_part0
  have h64 := extendCertifiedSegment 44416 32 32 h32 checkBlocks_44416_44479_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44480_44543_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44480_44543_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44480_44543 :
    ∀ i : Fin 64, indexedBlockCheck (44480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44480 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44480 0 32 h0 checkBlocks_44480_44543_part0
  have h64 := extendCertifiedSegment 44480 32 32 h32 checkBlocks_44480_44543_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44032_44543 :
    ∀ i : Fin 512, indexedBlockCheck (44032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44032 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 44032 0 64 h0 checkBlocks_44032_44095
  have h128 := extendCertifiedSegment 44032 64 64 h64 checkBlocks_44096_44159
  have h192 := extendCertifiedSegment 44032 128 64 h128 checkBlocks_44160_44223
  have h256 := extendCertifiedSegment 44032 192 64 h192 checkBlocks_44224_44287
  have h320 := extendCertifiedSegment 44032 256 64 h256 checkBlocks_44288_44351
  have h384 := extendCertifiedSegment 44032 320 64 h320 checkBlocks_44352_44415
  have h448 := extendCertifiedSegment 44032 384 64 h384 checkBlocks_44416_44479
  have h512 := extendCertifiedSegment 44032 448 64 h448 checkBlocks_44480_44543
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_44544_44607_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44544_44607_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44544_44607 :
    ∀ i : Fin 64, indexedBlockCheck (44544 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44544 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44544 0 32 h0 checkBlocks_44544_44607_part0
  have h64 := extendCertifiedSegment 44544 32 32 h32 checkBlocks_44544_44607_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44608_44671_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44608_44671_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44608_44671 :
    ∀ i : Fin 64, indexedBlockCheck (44608 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44608 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44608 0 32 h0 checkBlocks_44608_44671_part0
  have h64 := extendCertifiedSegment 44608 32 32 h32 checkBlocks_44608_44671_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44672_44735_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44672_44735_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44672_44735 :
    ∀ i : Fin 64, indexedBlockCheck (44672 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44672 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44672 0 32 h0 checkBlocks_44672_44735_part0
  have h64 := extendCertifiedSegment 44672 32 32 h32 checkBlocks_44672_44735_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44736_44799_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44736_44799_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44736_44799 :
    ∀ i : Fin 64, indexedBlockCheck (44736 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44736 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44736 0 32 h0 checkBlocks_44736_44799_part0
  have h64 := extendCertifiedSegment 44736 32 32 h32 checkBlocks_44736_44799_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44800_44863_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44800_44863_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44800_44863 :
    ∀ i : Fin 64, indexedBlockCheck (44800 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44800 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44800 0 32 h0 checkBlocks_44800_44863_part0
  have h64 := extendCertifiedSegment 44800 32 32 h32 checkBlocks_44800_44863_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44864_44927_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44864_44927_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44864_44927 :
    ∀ i : Fin 64, indexedBlockCheck (44864 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44864 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44864 0 32 h0 checkBlocks_44864_44927_part0
  have h64 := extendCertifiedSegment 44864 32 32 h32 checkBlocks_44864_44927_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44928_44991_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44928_44991_part1 :
    ∀ i : Fin 32, indexedBlockCheck (44960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44928_44991 :
    ∀ i : Fin 64, indexedBlockCheck (44928 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44928 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44928 0 32 h0 checkBlocks_44928_44991_part0
  have h64 := extendCertifiedSegment 44928 32 32 h32 checkBlocks_44928_44991_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44992_45055_part0 :
    ∀ i : Fin 32, indexedBlockCheck (44992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44992_45055_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44992_45055 :
    ∀ i : Fin 64, indexedBlockCheck (44992 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44992 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 44992 0 32 h0 checkBlocks_44992_45055_part0
  have h64 := extendCertifiedSegment 44992 32 32 h32 checkBlocks_44992_45055_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_44544_45055 :
    ∀ i : Fin 512, indexedBlockCheck (44544 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44544 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 44544 0 64 h0 checkBlocks_44544_44607
  have h128 := extendCertifiedSegment 44544 64 64 h64 checkBlocks_44608_44671
  have h192 := extendCertifiedSegment 44544 128 64 h128 checkBlocks_44672_44735
  have h256 := extendCertifiedSegment 44544 192 64 h192 checkBlocks_44736_44799
  have h320 := extendCertifiedSegment 44544 256 64 h256 checkBlocks_44800_44863
  have h384 := extendCertifiedSegment 44544 320 64 h320 checkBlocks_44864_44927
  have h448 := extendCertifiedSegment 44544 384 64 h384 checkBlocks_44928_44991
  have h512 := extendCertifiedSegment 44544 448 64 h448 checkBlocks_44992_45055
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_45056_45119_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45056_45119_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45056_45119 :
    ∀ i : Fin 64, indexedBlockCheck (45056 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45056 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45056 0 32 h0 checkBlocks_45056_45119_part0
  have h64 := extendCertifiedSegment 45056 32 32 h32 checkBlocks_45056_45119_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45120_45183_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45120_45183_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45120_45183 :
    ∀ i : Fin 64, indexedBlockCheck (45120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45120 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45120 0 32 h0 checkBlocks_45120_45183_part0
  have h64 := extendCertifiedSegment 45120 32 32 h32 checkBlocks_45120_45183_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45184_45247_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45184_45247_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45184_45247 :
    ∀ i : Fin 64, indexedBlockCheck (45184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45184 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45184 0 32 h0 checkBlocks_45184_45247_part0
  have h64 := extendCertifiedSegment 45184 32 32 h32 checkBlocks_45184_45247_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45248_45311_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45248_45311_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45248_45311 :
    ∀ i : Fin 64, indexedBlockCheck (45248 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45248 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45248 0 32 h0 checkBlocks_45248_45311_part0
  have h64 := extendCertifiedSegment 45248 32 32 h32 checkBlocks_45248_45311_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45312_45375_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45312_45375_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45312_45375 :
    ∀ i : Fin 64, indexedBlockCheck (45312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45312 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45312 0 32 h0 checkBlocks_45312_45375_part0
  have h64 := extendCertifiedSegment 45312 32 32 h32 checkBlocks_45312_45375_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45376_45439_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45376_45439_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45376_45439 :
    ∀ i : Fin 64, indexedBlockCheck (45376 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45376 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45376 0 32 h0 checkBlocks_45376_45439_part0
  have h64 := extendCertifiedSegment 45376 32 32 h32 checkBlocks_45376_45439_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45440_45503_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45440_45503_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45440_45503 :
    ∀ i : Fin 64, indexedBlockCheck (45440 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45440 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45440 0 32 h0 checkBlocks_45440_45503_part0
  have h64 := extendCertifiedSegment 45440 32 32 h32 checkBlocks_45440_45503_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45504_45567_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45504_45567_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45504_45567 :
    ∀ i : Fin 64, indexedBlockCheck (45504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45504 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45504 0 32 h0 checkBlocks_45504_45567_part0
  have h64 := extendCertifiedSegment 45504 32 32 h32 checkBlocks_45504_45567_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45056_45567 :
    ∀ i : Fin 512, indexedBlockCheck (45056 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45056 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 45056 0 64 h0 checkBlocks_45056_45119
  have h128 := extendCertifiedSegment 45056 64 64 h64 checkBlocks_45120_45183
  have h192 := extendCertifiedSegment 45056 128 64 h128 checkBlocks_45184_45247
  have h256 := extendCertifiedSegment 45056 192 64 h192 checkBlocks_45248_45311
  have h320 := extendCertifiedSegment 45056 256 64 h256 checkBlocks_45312_45375
  have h384 := extendCertifiedSegment 45056 320 64 h320 checkBlocks_45376_45439
  have h448 := extendCertifiedSegment 45056 384 64 h384 checkBlocks_45440_45503
  have h512 := extendCertifiedSegment 45056 448 64 h448 checkBlocks_45504_45567
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_45568_45631_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45568_45631_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45568_45631 :
    ∀ i : Fin 64, indexedBlockCheck (45568 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45568 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45568 0 32 h0 checkBlocks_45568_45631_part0
  have h64 := extendCertifiedSegment 45568 32 32 h32 checkBlocks_45568_45631_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45632_45695_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45632_45695_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45632_45695 :
    ∀ i : Fin 64, indexedBlockCheck (45632 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45632 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45632 0 32 h0 checkBlocks_45632_45695_part0
  have h64 := extendCertifiedSegment 45632 32 32 h32 checkBlocks_45632_45695_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45696_45759_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45696_45759_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45696_45759 :
    ∀ i : Fin 64, indexedBlockCheck (45696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45696 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45696 0 32 h0 checkBlocks_45696_45759_part0
  have h64 := extendCertifiedSegment 45696 32 32 h32 checkBlocks_45696_45759_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45760_45823_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45760_45823_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45760_45823 :
    ∀ i : Fin 64, indexedBlockCheck (45760 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45760 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45760 0 32 h0 checkBlocks_45760_45823_part0
  have h64 := extendCertifiedSegment 45760 32 32 h32 checkBlocks_45760_45823_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45824_45887_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45824_45887_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45824_45887 :
    ∀ i : Fin 64, indexedBlockCheck (45824 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45824 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45824 0 32 h0 checkBlocks_45824_45887_part0
  have h64 := extendCertifiedSegment 45824 32 32 h32 checkBlocks_45824_45887_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45888_45951_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45888_45951_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45888_45951 :
    ∀ i : Fin 64, indexedBlockCheck (45888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45888 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45888 0 32 h0 checkBlocks_45888_45951_part0
  have h64 := extendCertifiedSegment 45888 32 32 h32 checkBlocks_45888_45951_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45952_46015_part0 :
    ∀ i : Fin 32, indexedBlockCheck (45952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45952_46015_part1 :
    ∀ i : Fin 32, indexedBlockCheck (45984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45952_46015 :
    ∀ i : Fin 64, indexedBlockCheck (45952 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45952 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 45952 0 32 h0 checkBlocks_45952_46015_part0
  have h64 := extendCertifiedSegment 45952 32 32 h32 checkBlocks_45952_46015_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46016_46079_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46016_46079_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46016_46079 :
    ∀ i : Fin 64, indexedBlockCheck (46016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46016 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46016 0 32 h0 checkBlocks_46016_46079_part0
  have h64 := extendCertifiedSegment 46016 32 32 h32 checkBlocks_46016_46079_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_45568_46079 :
    ∀ i : Fin 512, indexedBlockCheck (45568 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45568 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 45568 0 64 h0 checkBlocks_45568_45631
  have h128 := extendCertifiedSegment 45568 64 64 h64 checkBlocks_45632_45695
  have h192 := extendCertifiedSegment 45568 128 64 h128 checkBlocks_45696_45759
  have h256 := extendCertifiedSegment 45568 192 64 h192 checkBlocks_45760_45823
  have h320 := extendCertifiedSegment 45568 256 64 h256 checkBlocks_45824_45887
  have h384 := extendCertifiedSegment 45568 320 64 h320 checkBlocks_45888_45951
  have h448 := extendCertifiedSegment 45568 384 64 h384 checkBlocks_45952_46015
  have h512 := extendCertifiedSegment 45568 448 64 h448 checkBlocks_46016_46079
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [44032, 46080) passes the packed checker. -/
public theorem blocks_in_44032_46080 :
    ∀ i : Fin 2048, indexedBlockCheck (44032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44032 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 44032 0 512 h0 checkBlocks_44032_44543
  have h1024 := extendCertifiedSegment 44032 512 512 h512 checkBlocks_44544_45055
  have h1536 := extendCertifiedSegment 44032 1024 512 h1024 checkBlocks_45056_45567
  have h2048 := extendCertifiedSegment 44032 1536 512 h1536 checkBlocks_45568_46079
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
