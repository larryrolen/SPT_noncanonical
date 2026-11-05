/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 76800 through 78847 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_76800_76863_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76800_76863_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76800_76863 :
    ∀ i : Fin 64, indexedBlockCheck (76800 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76800 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76800 0 32 h0 checkBlocks_76800_76863_part0
  have h64 := extendCertifiedSegment 76800 32 32 h32 checkBlocks_76800_76863_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76864_76927_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76864_76927_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76864_76927 :
    ∀ i : Fin 64, indexedBlockCheck (76864 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76864 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76864 0 32 h0 checkBlocks_76864_76927_part0
  have h64 := extendCertifiedSegment 76864 32 32 h32 checkBlocks_76864_76927_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76928_76991_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76928_76991_part1 :
    ∀ i : Fin 32, indexedBlockCheck (76960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76928_76991 :
    ∀ i : Fin 64, indexedBlockCheck (76928 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76928 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76928 0 32 h0 checkBlocks_76928_76991_part0
  have h64 := extendCertifiedSegment 76928 32 32 h32 checkBlocks_76928_76991_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76992_77055_part0 :
    ∀ i : Fin 32, indexedBlockCheck (76992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76992_77055_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_76992_77055 :
    ∀ i : Fin 64, indexedBlockCheck (76992 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76992 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 76992 0 32 h0 checkBlocks_76992_77055_part0
  have h64 := extendCertifiedSegment 76992 32 32 h32 checkBlocks_76992_77055_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77056_77119_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77056_77119_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77056_77119 :
    ∀ i : Fin 64, indexedBlockCheck (77056 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77056 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77056 0 32 h0 checkBlocks_77056_77119_part0
  have h64 := extendCertifiedSegment 77056 32 32 h32 checkBlocks_77056_77119_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77120_77183_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77120_77183_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77120_77183 :
    ∀ i : Fin 64, indexedBlockCheck (77120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77120 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77120 0 32 h0 checkBlocks_77120_77183_part0
  have h64 := extendCertifiedSegment 77120 32 32 h32 checkBlocks_77120_77183_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77184_77247_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77184_77247_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77184_77247 :
    ∀ i : Fin 64, indexedBlockCheck (77184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77184 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77184 0 32 h0 checkBlocks_77184_77247_part0
  have h64 := extendCertifiedSegment 77184 32 32 h32 checkBlocks_77184_77247_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77248_77311_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77248_77311_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77248_77311 :
    ∀ i : Fin 64, indexedBlockCheck (77248 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77248 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77248 0 32 h0 checkBlocks_77248_77311_part0
  have h64 := extendCertifiedSegment 77248 32 32 h32 checkBlocks_77248_77311_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_76800_77311 :
    ∀ i : Fin 512, indexedBlockCheck (76800 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76800 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 76800 0 64 h0 checkBlocks_76800_76863
  have h128 := extendCertifiedSegment 76800 64 64 h64 checkBlocks_76864_76927
  have h192 := extendCertifiedSegment 76800 128 64 h128 checkBlocks_76928_76991
  have h256 := extendCertifiedSegment 76800 192 64 h192 checkBlocks_76992_77055
  have h320 := extendCertifiedSegment 76800 256 64 h256 checkBlocks_77056_77119
  have h384 := extendCertifiedSegment 76800 320 64 h320 checkBlocks_77120_77183
  have h448 := extendCertifiedSegment 76800 384 64 h384 checkBlocks_77184_77247
  have h512 := extendCertifiedSegment 76800 448 64 h448 checkBlocks_77248_77311
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_77312_77375_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77312_77375_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77312_77375 :
    ∀ i : Fin 64, indexedBlockCheck (77312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77312 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77312 0 32 h0 checkBlocks_77312_77375_part0
  have h64 := extendCertifiedSegment 77312 32 32 h32 checkBlocks_77312_77375_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77376_77439_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77376_77439_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77376_77439 :
    ∀ i : Fin 64, indexedBlockCheck (77376 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77376 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77376 0 32 h0 checkBlocks_77376_77439_part0
  have h64 := extendCertifiedSegment 77376 32 32 h32 checkBlocks_77376_77439_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77440_77503_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77440_77503_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77440_77503 :
    ∀ i : Fin 64, indexedBlockCheck (77440 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77440 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77440 0 32 h0 checkBlocks_77440_77503_part0
  have h64 := extendCertifiedSegment 77440 32 32 h32 checkBlocks_77440_77503_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77504_77567_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77504_77567_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77504_77567 :
    ∀ i : Fin 64, indexedBlockCheck (77504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77504 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77504 0 32 h0 checkBlocks_77504_77567_part0
  have h64 := extendCertifiedSegment 77504 32 32 h32 checkBlocks_77504_77567_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77568_77631_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77568_77631_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77568_77631 :
    ∀ i : Fin 64, indexedBlockCheck (77568 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77568 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77568 0 32 h0 checkBlocks_77568_77631_part0
  have h64 := extendCertifiedSegment 77568 32 32 h32 checkBlocks_77568_77631_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77632_77695_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77632_77695_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77632_77695 :
    ∀ i : Fin 64, indexedBlockCheck (77632 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77632 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77632 0 32 h0 checkBlocks_77632_77695_part0
  have h64 := extendCertifiedSegment 77632 32 32 h32 checkBlocks_77632_77695_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77696_77759_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77696_77759_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77696_77759 :
    ∀ i : Fin 64, indexedBlockCheck (77696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77696 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77696 0 32 h0 checkBlocks_77696_77759_part0
  have h64 := extendCertifiedSegment 77696 32 32 h32 checkBlocks_77696_77759_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77760_77823_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77760_77823_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77760_77823 :
    ∀ i : Fin 64, indexedBlockCheck (77760 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77760 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77760 0 32 h0 checkBlocks_77760_77823_part0
  have h64 := extendCertifiedSegment 77760 32 32 h32 checkBlocks_77760_77823_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77312_77823 :
    ∀ i : Fin 512, indexedBlockCheck (77312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77312 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 77312 0 64 h0 checkBlocks_77312_77375
  have h128 := extendCertifiedSegment 77312 64 64 h64 checkBlocks_77376_77439
  have h192 := extendCertifiedSegment 77312 128 64 h128 checkBlocks_77440_77503
  have h256 := extendCertifiedSegment 77312 192 64 h192 checkBlocks_77504_77567
  have h320 := extendCertifiedSegment 77312 256 64 h256 checkBlocks_77568_77631
  have h384 := extendCertifiedSegment 77312 320 64 h320 checkBlocks_77632_77695
  have h448 := extendCertifiedSegment 77312 384 64 h384 checkBlocks_77696_77759
  have h512 := extendCertifiedSegment 77312 448 64 h448 checkBlocks_77760_77823
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_77824_77887_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77824_77887_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77824_77887 :
    ∀ i : Fin 64, indexedBlockCheck (77824 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77824 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77824 0 32 h0 checkBlocks_77824_77887_part0
  have h64 := extendCertifiedSegment 77824 32 32 h32 checkBlocks_77824_77887_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77888_77951_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77888_77951_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77888_77951 :
    ∀ i : Fin 64, indexedBlockCheck (77888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77888 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77888 0 32 h0 checkBlocks_77888_77951_part0
  have h64 := extendCertifiedSegment 77888 32 32 h32 checkBlocks_77888_77951_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77952_78015_part0 :
    ∀ i : Fin 32, indexedBlockCheck (77952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77952_78015_part1 :
    ∀ i : Fin 32, indexedBlockCheck (77984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_77952_78015 :
    ∀ i : Fin 64, indexedBlockCheck (77952 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77952 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 77952 0 32 h0 checkBlocks_77952_78015_part0
  have h64 := extendCertifiedSegment 77952 32 32 h32 checkBlocks_77952_78015_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78016_78079_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78016_78079_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78016_78079 :
    ∀ i : Fin 64, indexedBlockCheck (78016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78016 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78016 0 32 h0 checkBlocks_78016_78079_part0
  have h64 := extendCertifiedSegment 78016 32 32 h32 checkBlocks_78016_78079_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78080_78143_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78080_78143_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78080_78143 :
    ∀ i : Fin 64, indexedBlockCheck (78080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78080 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78080 0 32 h0 checkBlocks_78080_78143_part0
  have h64 := extendCertifiedSegment 78080 32 32 h32 checkBlocks_78080_78143_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78144_78207_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78144_78207_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78144_78207 :
    ∀ i : Fin 64, indexedBlockCheck (78144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78144 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78144 0 32 h0 checkBlocks_78144_78207_part0
  have h64 := extendCertifiedSegment 78144 32 32 h32 checkBlocks_78144_78207_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78208_78271_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78208_78271_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78208_78271 :
    ∀ i : Fin 64, indexedBlockCheck (78208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78208 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78208 0 32 h0 checkBlocks_78208_78271_part0
  have h64 := extendCertifiedSegment 78208 32 32 h32 checkBlocks_78208_78271_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78272_78335_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78272_78335_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78272_78335 :
    ∀ i : Fin 64, indexedBlockCheck (78272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78272 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78272 0 32 h0 checkBlocks_78272_78335_part0
  have h64 := extendCertifiedSegment 78272 32 32 h32 checkBlocks_78272_78335_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_77824_78335 :
    ∀ i : Fin 512, indexedBlockCheck (77824 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (77824 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 77824 0 64 h0 checkBlocks_77824_77887
  have h128 := extendCertifiedSegment 77824 64 64 h64 checkBlocks_77888_77951
  have h192 := extendCertifiedSegment 77824 128 64 h128 checkBlocks_77952_78015
  have h256 := extendCertifiedSegment 77824 192 64 h192 checkBlocks_78016_78079
  have h320 := extendCertifiedSegment 77824 256 64 h256 checkBlocks_78080_78143
  have h384 := extendCertifiedSegment 77824 320 64 h320 checkBlocks_78144_78207
  have h448 := extendCertifiedSegment 77824 384 64 h384 checkBlocks_78208_78271
  have h512 := extendCertifiedSegment 77824 448 64 h448 checkBlocks_78272_78335
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_78336_78399_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78336_78399_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78336_78399 :
    ∀ i : Fin 64, indexedBlockCheck (78336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78336 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78336 0 32 h0 checkBlocks_78336_78399_part0
  have h64 := extendCertifiedSegment 78336 32 32 h32 checkBlocks_78336_78399_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78400_78463_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78400_78463_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78400_78463 :
    ∀ i : Fin 64, indexedBlockCheck (78400 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78400 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78400 0 32 h0 checkBlocks_78400_78463_part0
  have h64 := extendCertifiedSegment 78400 32 32 h32 checkBlocks_78400_78463_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78464_78527_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78464_78527_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78464_78527 :
    ∀ i : Fin 64, indexedBlockCheck (78464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78464 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78464 0 32 h0 checkBlocks_78464_78527_part0
  have h64 := extendCertifiedSegment 78464 32 32 h32 checkBlocks_78464_78527_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78528_78591_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78528_78591_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78528_78591 :
    ∀ i : Fin 64, indexedBlockCheck (78528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78528 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78528 0 32 h0 checkBlocks_78528_78591_part0
  have h64 := extendCertifiedSegment 78528 32 32 h32 checkBlocks_78528_78591_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78592_78655_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78592_78655_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78592_78655 :
    ∀ i : Fin 64, indexedBlockCheck (78592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78592 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78592 0 32 h0 checkBlocks_78592_78655_part0
  have h64 := extendCertifiedSegment 78592 32 32 h32 checkBlocks_78592_78655_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78656_78719_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78656_78719_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78656_78719 :
    ∀ i : Fin 64, indexedBlockCheck (78656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78656 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78656 0 32 h0 checkBlocks_78656_78719_part0
  have h64 := extendCertifiedSegment 78656 32 32 h32 checkBlocks_78656_78719_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78720_78783_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78720_78783_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78720_78783 :
    ∀ i : Fin 64, indexedBlockCheck (78720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78720 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78720 0 32 h0 checkBlocks_78720_78783_part0
  have h64 := extendCertifiedSegment 78720 32 32 h32 checkBlocks_78720_78783_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78784_78847_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78784_78847_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78784_78847 :
    ∀ i : Fin 64, indexedBlockCheck (78784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78784 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78784 0 32 h0 checkBlocks_78784_78847_part0
  have h64 := extendCertifiedSegment 78784 32 32 h32 checkBlocks_78784_78847_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78336_78847 :
    ∀ i : Fin 512, indexedBlockCheck (78336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78336 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 78336 0 64 h0 checkBlocks_78336_78399
  have h128 := extendCertifiedSegment 78336 64 64 h64 checkBlocks_78400_78463
  have h192 := extendCertifiedSegment 78336 128 64 h128 checkBlocks_78464_78527
  have h256 := extendCertifiedSegment 78336 192 64 h192 checkBlocks_78528_78591
  have h320 := extendCertifiedSegment 78336 256 64 h256 checkBlocks_78592_78655
  have h384 := extendCertifiedSegment 78336 320 64 h320 checkBlocks_78656_78719
  have h448 := extendCertifiedSegment 78336 384 64 h384 checkBlocks_78720_78783
  have h512 := extendCertifiedSegment 78336 448 64 h448 checkBlocks_78784_78847
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [76800, 78848) passes the packed checker. -/
public theorem blocks_in_76800_78848 :
    ∀ i : Fin 2048, indexedBlockCheck (76800 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (76800 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 76800 0 512 h0 checkBlocks_76800_77311
  have h1024 := extendCertifiedSegment 76800 512 512 h512 checkBlocks_77312_77823
  have h1536 := extendCertifiedSegment 76800 1024 512 h1024 checkBlocks_77824_78335
  have h2048 := extendCertifiedSegment 76800 1536 512 h1536 checkBlocks_78336_78847
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
