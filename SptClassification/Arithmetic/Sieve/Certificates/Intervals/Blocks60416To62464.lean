/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 60416 through 62463 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_60416_60479_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60416_60479_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60416_60479 :
    ∀ i : Fin 64, indexedBlockCheck (60416 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60416 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60416 0 32 h0 checkBlocks_60416_60479_part0
  have h64 := extendCertifiedSegment 60416 32 32 h32 checkBlocks_60416_60479_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60480_60543_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60480_60543_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60480_60543 :
    ∀ i : Fin 64, indexedBlockCheck (60480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60480 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60480 0 32 h0 checkBlocks_60480_60543_part0
  have h64 := extendCertifiedSegment 60480 32 32 h32 checkBlocks_60480_60543_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60544_60607_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60544_60607_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60544_60607 :
    ∀ i : Fin 64, indexedBlockCheck (60544 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60544 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60544 0 32 h0 checkBlocks_60544_60607_part0
  have h64 := extendCertifiedSegment 60544 32 32 h32 checkBlocks_60544_60607_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60608_60671_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60608_60671_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60608_60671 :
    ∀ i : Fin 64, indexedBlockCheck (60608 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60608 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60608 0 32 h0 checkBlocks_60608_60671_part0
  have h64 := extendCertifiedSegment 60608 32 32 h32 checkBlocks_60608_60671_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60672_60735_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60672_60735_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60672_60735 :
    ∀ i : Fin 64, indexedBlockCheck (60672 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60672 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60672 0 32 h0 checkBlocks_60672_60735_part0
  have h64 := extendCertifiedSegment 60672 32 32 h32 checkBlocks_60672_60735_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60736_60799_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60736_60799_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60736_60799 :
    ∀ i : Fin 64, indexedBlockCheck (60736 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60736 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60736 0 32 h0 checkBlocks_60736_60799_part0
  have h64 := extendCertifiedSegment 60736 32 32 h32 checkBlocks_60736_60799_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60800_60863_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60800_60863_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60800_60863 :
    ∀ i : Fin 64, indexedBlockCheck (60800 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60800 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60800 0 32 h0 checkBlocks_60800_60863_part0
  have h64 := extendCertifiedSegment 60800 32 32 h32 checkBlocks_60800_60863_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60864_60927_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60864_60927_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60864_60927 :
    ∀ i : Fin 64, indexedBlockCheck (60864 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60864 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60864 0 32 h0 checkBlocks_60864_60927_part0
  have h64 := extendCertifiedSegment 60864 32 32 h32 checkBlocks_60864_60927_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60416_60927 :
    ∀ i : Fin 512, indexedBlockCheck (60416 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60416 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 60416 0 64 h0 checkBlocks_60416_60479
  have h128 := extendCertifiedSegment 60416 64 64 h64 checkBlocks_60480_60543
  have h192 := extendCertifiedSegment 60416 128 64 h128 checkBlocks_60544_60607
  have h256 := extendCertifiedSegment 60416 192 64 h192 checkBlocks_60608_60671
  have h320 := extendCertifiedSegment 60416 256 64 h256 checkBlocks_60672_60735
  have h384 := extendCertifiedSegment 60416 320 64 h320 checkBlocks_60736_60799
  have h448 := extendCertifiedSegment 60416 384 64 h384 checkBlocks_60800_60863
  have h512 := extendCertifiedSegment 60416 448 64 h448 checkBlocks_60864_60927
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_60928_60991_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60928_60991_part1 :
    ∀ i : Fin 32, indexedBlockCheck (60960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60928_60991 :
    ∀ i : Fin 64, indexedBlockCheck (60928 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60928 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60928 0 32 h0 checkBlocks_60928_60991_part0
  have h64 := extendCertifiedSegment 60928 32 32 h32 checkBlocks_60928_60991_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60992_61055_part0 :
    ∀ i : Fin 32, indexedBlockCheck (60992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60992_61055_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_60992_61055 :
    ∀ i : Fin 64, indexedBlockCheck (60992 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60992 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 60992 0 32 h0 checkBlocks_60992_61055_part0
  have h64 := extendCertifiedSegment 60992 32 32 h32 checkBlocks_60992_61055_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61056_61119_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61056_61119_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61056_61119 :
    ∀ i : Fin 64, indexedBlockCheck (61056 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61056 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61056 0 32 h0 checkBlocks_61056_61119_part0
  have h64 := extendCertifiedSegment 61056 32 32 h32 checkBlocks_61056_61119_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61120_61183_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61120_61183_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61120_61183 :
    ∀ i : Fin 64, indexedBlockCheck (61120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61120 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61120 0 32 h0 checkBlocks_61120_61183_part0
  have h64 := extendCertifiedSegment 61120 32 32 h32 checkBlocks_61120_61183_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61184_61247_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61184_61247_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61184_61247 :
    ∀ i : Fin 64, indexedBlockCheck (61184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61184 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61184 0 32 h0 checkBlocks_61184_61247_part0
  have h64 := extendCertifiedSegment 61184 32 32 h32 checkBlocks_61184_61247_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61248_61311_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61248_61311_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61248_61311 :
    ∀ i : Fin 64, indexedBlockCheck (61248 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61248 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61248 0 32 h0 checkBlocks_61248_61311_part0
  have h64 := extendCertifiedSegment 61248 32 32 h32 checkBlocks_61248_61311_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61312_61375_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61312_61375_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61312_61375 :
    ∀ i : Fin 64, indexedBlockCheck (61312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61312 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61312 0 32 h0 checkBlocks_61312_61375_part0
  have h64 := extendCertifiedSegment 61312 32 32 h32 checkBlocks_61312_61375_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61376_61439_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61376_61439_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61376_61439 :
    ∀ i : Fin 64, indexedBlockCheck (61376 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61376 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61376 0 32 h0 checkBlocks_61376_61439_part0
  have h64 := extendCertifiedSegment 61376 32 32 h32 checkBlocks_61376_61439_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_60928_61439 :
    ∀ i : Fin 512, indexedBlockCheck (60928 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60928 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 60928 0 64 h0 checkBlocks_60928_60991
  have h128 := extendCertifiedSegment 60928 64 64 h64 checkBlocks_60992_61055
  have h192 := extendCertifiedSegment 60928 128 64 h128 checkBlocks_61056_61119
  have h256 := extendCertifiedSegment 60928 192 64 h192 checkBlocks_61120_61183
  have h320 := extendCertifiedSegment 60928 256 64 h256 checkBlocks_61184_61247
  have h384 := extendCertifiedSegment 60928 320 64 h320 checkBlocks_61248_61311
  have h448 := extendCertifiedSegment 60928 384 64 h384 checkBlocks_61312_61375
  have h512 := extendCertifiedSegment 60928 448 64 h448 checkBlocks_61376_61439
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_61440_61503_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61440_61503_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61440_61503 :
    ∀ i : Fin 64, indexedBlockCheck (61440 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61440 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61440 0 32 h0 checkBlocks_61440_61503_part0
  have h64 := extendCertifiedSegment 61440 32 32 h32 checkBlocks_61440_61503_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61504_61567_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61504_61567_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61504_61567 :
    ∀ i : Fin 64, indexedBlockCheck (61504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61504 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61504 0 32 h0 checkBlocks_61504_61567_part0
  have h64 := extendCertifiedSegment 61504 32 32 h32 checkBlocks_61504_61567_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61568_61631_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61568_61631_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61568_61631 :
    ∀ i : Fin 64, indexedBlockCheck (61568 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61568 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61568 0 32 h0 checkBlocks_61568_61631_part0
  have h64 := extendCertifiedSegment 61568 32 32 h32 checkBlocks_61568_61631_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61632_61695_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61632_61695_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61632_61695 :
    ∀ i : Fin 64, indexedBlockCheck (61632 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61632 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61632 0 32 h0 checkBlocks_61632_61695_part0
  have h64 := extendCertifiedSegment 61632 32 32 h32 checkBlocks_61632_61695_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61696_61759_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61696_61759_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61696_61759 :
    ∀ i : Fin 64, indexedBlockCheck (61696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61696 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61696 0 32 h0 checkBlocks_61696_61759_part0
  have h64 := extendCertifiedSegment 61696 32 32 h32 checkBlocks_61696_61759_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61760_61823_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61760_61823_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61760_61823 :
    ∀ i : Fin 64, indexedBlockCheck (61760 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61760 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61760 0 32 h0 checkBlocks_61760_61823_part0
  have h64 := extendCertifiedSegment 61760 32 32 h32 checkBlocks_61760_61823_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61824_61887_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61824_61887_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61824_61887 :
    ∀ i : Fin 64, indexedBlockCheck (61824 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61824 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61824 0 32 h0 checkBlocks_61824_61887_part0
  have h64 := extendCertifiedSegment 61824 32 32 h32 checkBlocks_61824_61887_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61888_61951_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61888_61951_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61888_61951 :
    ∀ i : Fin 64, indexedBlockCheck (61888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61888 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61888 0 32 h0 checkBlocks_61888_61951_part0
  have h64 := extendCertifiedSegment 61888 32 32 h32 checkBlocks_61888_61951_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61440_61951 :
    ∀ i : Fin 512, indexedBlockCheck (61440 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61440 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 61440 0 64 h0 checkBlocks_61440_61503
  have h128 := extendCertifiedSegment 61440 64 64 h64 checkBlocks_61504_61567
  have h192 := extendCertifiedSegment 61440 128 64 h128 checkBlocks_61568_61631
  have h256 := extendCertifiedSegment 61440 192 64 h192 checkBlocks_61632_61695
  have h320 := extendCertifiedSegment 61440 256 64 h256 checkBlocks_61696_61759
  have h384 := extendCertifiedSegment 61440 320 64 h320 checkBlocks_61760_61823
  have h448 := extendCertifiedSegment 61440 384 64 h384 checkBlocks_61824_61887
  have h512 := extendCertifiedSegment 61440 448 64 h448 checkBlocks_61888_61951
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_61952_62015_part0 :
    ∀ i : Fin 32, indexedBlockCheck (61952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61952_62015_part1 :
    ∀ i : Fin 32, indexedBlockCheck (61984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_61952_62015 :
    ∀ i : Fin 64, indexedBlockCheck (61952 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61952 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 61952 0 32 h0 checkBlocks_61952_62015_part0
  have h64 := extendCertifiedSegment 61952 32 32 h32 checkBlocks_61952_62015_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62016_62079_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62016_62079_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62016_62079 :
    ∀ i : Fin 64, indexedBlockCheck (62016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62016 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62016 0 32 h0 checkBlocks_62016_62079_part0
  have h64 := extendCertifiedSegment 62016 32 32 h32 checkBlocks_62016_62079_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62080_62143_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62080_62143_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62080_62143 :
    ∀ i : Fin 64, indexedBlockCheck (62080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62080 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62080 0 32 h0 checkBlocks_62080_62143_part0
  have h64 := extendCertifiedSegment 62080 32 32 h32 checkBlocks_62080_62143_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62144_62207_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62144_62207_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62144_62207 :
    ∀ i : Fin 64, indexedBlockCheck (62144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62144 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62144 0 32 h0 checkBlocks_62144_62207_part0
  have h64 := extendCertifiedSegment 62144 32 32 h32 checkBlocks_62144_62207_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62208_62271_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62208_62271_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62208_62271 :
    ∀ i : Fin 64, indexedBlockCheck (62208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62208 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62208 0 32 h0 checkBlocks_62208_62271_part0
  have h64 := extendCertifiedSegment 62208 32 32 h32 checkBlocks_62208_62271_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62272_62335_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62272_62335_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62272_62335 :
    ∀ i : Fin 64, indexedBlockCheck (62272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62272 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62272 0 32 h0 checkBlocks_62272_62335_part0
  have h64 := extendCertifiedSegment 62272 32 32 h32 checkBlocks_62272_62335_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62336_62399_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62336_62399_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62336_62399 :
    ∀ i : Fin 64, indexedBlockCheck (62336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62336 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62336 0 32 h0 checkBlocks_62336_62399_part0
  have h64 := extendCertifiedSegment 62336 32 32 h32 checkBlocks_62336_62399_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62400_62463_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62400_62463_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62400_62463 :
    ∀ i : Fin 64, indexedBlockCheck (62400 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62400 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62400 0 32 h0 checkBlocks_62400_62463_part0
  have h64 := extendCertifiedSegment 62400 32 32 h32 checkBlocks_62400_62463_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_61952_62463 :
    ∀ i : Fin 512, indexedBlockCheck (61952 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (61952 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 61952 0 64 h0 checkBlocks_61952_62015
  have h128 := extendCertifiedSegment 61952 64 64 h64 checkBlocks_62016_62079
  have h192 := extendCertifiedSegment 61952 128 64 h128 checkBlocks_62080_62143
  have h256 := extendCertifiedSegment 61952 192 64 h192 checkBlocks_62144_62207
  have h320 := extendCertifiedSegment 61952 256 64 h256 checkBlocks_62208_62271
  have h384 := extendCertifiedSegment 61952 320 64 h320 checkBlocks_62272_62335
  have h448 := extendCertifiedSegment 61952 384 64 h384 checkBlocks_62336_62399
  have h512 := extendCertifiedSegment 61952 448 64 h448 checkBlocks_62400_62463
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [60416, 62464) passes the packed checker. -/
public theorem blocks_in_60416_62464 :
    ∀ i : Fin 2048, indexedBlockCheck (60416 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (60416 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 60416 0 512 h0 checkBlocks_60416_60927
  have h1024 := extendCertifiedSegment 60416 512 512 h512 checkBlocks_60928_61439
  have h1536 := extendCertifiedSegment 60416 1024 512 h1024 checkBlocks_61440_61951
  have h2048 := extendCertifiedSegment 60416 1536 512 h1536 checkBlocks_61952_62463
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
