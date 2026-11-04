/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 93184 through 95231 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_93184_93247_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93184_93247_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93184_93247 :
    ∀ i : Fin 64, indexedBlockCheck (93184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93184 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93184 0 32 h0 checkBlocks_93184_93247_part0
  have h64 := extendCertifiedSegment 93184 32 32 h32 checkBlocks_93184_93247_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93248_93311_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93248_93311_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93248_93311 :
    ∀ i : Fin 64, indexedBlockCheck (93248 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93248 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93248 0 32 h0 checkBlocks_93248_93311_part0
  have h64 := extendCertifiedSegment 93248 32 32 h32 checkBlocks_93248_93311_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93312_93375_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93312_93375_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93312_93375 :
    ∀ i : Fin 64, indexedBlockCheck (93312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93312 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93312 0 32 h0 checkBlocks_93312_93375_part0
  have h64 := extendCertifiedSegment 93312 32 32 h32 checkBlocks_93312_93375_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93376_93439_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93376_93439_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93376_93439 :
    ∀ i : Fin 64, indexedBlockCheck (93376 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93376 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93376 0 32 h0 checkBlocks_93376_93439_part0
  have h64 := extendCertifiedSegment 93376 32 32 h32 checkBlocks_93376_93439_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93440_93503_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93440_93503_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93440_93503 :
    ∀ i : Fin 64, indexedBlockCheck (93440 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93440 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93440 0 32 h0 checkBlocks_93440_93503_part0
  have h64 := extendCertifiedSegment 93440 32 32 h32 checkBlocks_93440_93503_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93504_93567_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93504_93567_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93504_93567 :
    ∀ i : Fin 64, indexedBlockCheck (93504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93504 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93504 0 32 h0 checkBlocks_93504_93567_part0
  have h64 := extendCertifiedSegment 93504 32 32 h32 checkBlocks_93504_93567_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93568_93631_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93568_93631_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93568_93631 :
    ∀ i : Fin 64, indexedBlockCheck (93568 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93568 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93568 0 32 h0 checkBlocks_93568_93631_part0
  have h64 := extendCertifiedSegment 93568 32 32 h32 checkBlocks_93568_93631_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93632_93695_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93632_93695_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93632_93695 :
    ∀ i : Fin 64, indexedBlockCheck (93632 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93632 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93632 0 32 h0 checkBlocks_93632_93695_part0
  have h64 := extendCertifiedSegment 93632 32 32 h32 checkBlocks_93632_93695_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93184_93695 :
    ∀ i : Fin 512, indexedBlockCheck (93184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93184 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 93184 0 64 h0 checkBlocks_93184_93247
  have h128 := extendCertifiedSegment 93184 64 64 h64 checkBlocks_93248_93311
  have h192 := extendCertifiedSegment 93184 128 64 h128 checkBlocks_93312_93375
  have h256 := extendCertifiedSegment 93184 192 64 h192 checkBlocks_93376_93439
  have h320 := extendCertifiedSegment 93184 256 64 h256 checkBlocks_93440_93503
  have h384 := extendCertifiedSegment 93184 320 64 h320 checkBlocks_93504_93567
  have h448 := extendCertifiedSegment 93184 384 64 h384 checkBlocks_93568_93631
  have h512 := extendCertifiedSegment 93184 448 64 h448 checkBlocks_93632_93695
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_93696_93759_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93696_93759_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93696_93759 :
    ∀ i : Fin 64, indexedBlockCheck (93696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93696 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93696 0 32 h0 checkBlocks_93696_93759_part0
  have h64 := extendCertifiedSegment 93696 32 32 h32 checkBlocks_93696_93759_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93760_93823_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93760_93823_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93760_93823 :
    ∀ i : Fin 64, indexedBlockCheck (93760 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93760 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93760 0 32 h0 checkBlocks_93760_93823_part0
  have h64 := extendCertifiedSegment 93760 32 32 h32 checkBlocks_93760_93823_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93824_93887_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93824_93887_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93824_93887 :
    ∀ i : Fin 64, indexedBlockCheck (93824 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93824 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93824 0 32 h0 checkBlocks_93824_93887_part0
  have h64 := extendCertifiedSegment 93824 32 32 h32 checkBlocks_93824_93887_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93888_93951_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93888_93951_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93888_93951 :
    ∀ i : Fin 64, indexedBlockCheck (93888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93888 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93888 0 32 h0 checkBlocks_93888_93951_part0
  have h64 := extendCertifiedSegment 93888 32 32 h32 checkBlocks_93888_93951_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93952_94015_part0 :
    ∀ i : Fin 32, indexedBlockCheck (93952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93952_94015_part1 :
    ∀ i : Fin 32, indexedBlockCheck (93984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93952_94015 :
    ∀ i : Fin 64, indexedBlockCheck (93952 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93952 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 93952 0 32 h0 checkBlocks_93952_94015_part0
  have h64 := extendCertifiedSegment 93952 32 32 h32 checkBlocks_93952_94015_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94016_94079_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94016_94079_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94016_94079 :
    ∀ i : Fin 64, indexedBlockCheck (94016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94016 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94016 0 32 h0 checkBlocks_94016_94079_part0
  have h64 := extendCertifiedSegment 94016 32 32 h32 checkBlocks_94016_94079_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94080_94143_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94080_94143_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94080_94143 :
    ∀ i : Fin 64, indexedBlockCheck (94080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94080 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94080 0 32 h0 checkBlocks_94080_94143_part0
  have h64 := extendCertifiedSegment 94080 32 32 h32 checkBlocks_94080_94143_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94144_94207_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94144_94207_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94144_94207 :
    ∀ i : Fin 64, indexedBlockCheck (94144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94144 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94144 0 32 h0 checkBlocks_94144_94207_part0
  have h64 := extendCertifiedSegment 94144 32 32 h32 checkBlocks_94144_94207_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_93696_94207 :
    ∀ i : Fin 512, indexedBlockCheck (93696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93696 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 93696 0 64 h0 checkBlocks_93696_93759
  have h128 := extendCertifiedSegment 93696 64 64 h64 checkBlocks_93760_93823
  have h192 := extendCertifiedSegment 93696 128 64 h128 checkBlocks_93824_93887
  have h256 := extendCertifiedSegment 93696 192 64 h192 checkBlocks_93888_93951
  have h320 := extendCertifiedSegment 93696 256 64 h256 checkBlocks_93952_94015
  have h384 := extendCertifiedSegment 93696 320 64 h320 checkBlocks_94016_94079
  have h448 := extendCertifiedSegment 93696 384 64 h384 checkBlocks_94080_94143
  have h512 := extendCertifiedSegment 93696 448 64 h448 checkBlocks_94144_94207
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_94208_94271_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94208_94271_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94208_94271 :
    ∀ i : Fin 64, indexedBlockCheck (94208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94208 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94208 0 32 h0 checkBlocks_94208_94271_part0
  have h64 := extendCertifiedSegment 94208 32 32 h32 checkBlocks_94208_94271_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94272_94335_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94272_94335_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94272_94335 :
    ∀ i : Fin 64, indexedBlockCheck (94272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94272 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94272 0 32 h0 checkBlocks_94272_94335_part0
  have h64 := extendCertifiedSegment 94272 32 32 h32 checkBlocks_94272_94335_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94336_94399_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94336_94399_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94336_94399 :
    ∀ i : Fin 64, indexedBlockCheck (94336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94336 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94336 0 32 h0 checkBlocks_94336_94399_part0
  have h64 := extendCertifiedSegment 94336 32 32 h32 checkBlocks_94336_94399_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94400_94463_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94400_94463_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94400_94463 :
    ∀ i : Fin 64, indexedBlockCheck (94400 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94400 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94400 0 32 h0 checkBlocks_94400_94463_part0
  have h64 := extendCertifiedSegment 94400 32 32 h32 checkBlocks_94400_94463_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94464_94527_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94464_94527_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94464_94527 :
    ∀ i : Fin 64, indexedBlockCheck (94464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94464 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94464 0 32 h0 checkBlocks_94464_94527_part0
  have h64 := extendCertifiedSegment 94464 32 32 h32 checkBlocks_94464_94527_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94528_94591_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94528_94591_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94528_94591 :
    ∀ i : Fin 64, indexedBlockCheck (94528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94528 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94528 0 32 h0 checkBlocks_94528_94591_part0
  have h64 := extendCertifiedSegment 94528 32 32 h32 checkBlocks_94528_94591_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94592_94655_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94592_94655_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94592_94655 :
    ∀ i : Fin 64, indexedBlockCheck (94592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94592 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94592 0 32 h0 checkBlocks_94592_94655_part0
  have h64 := extendCertifiedSegment 94592 32 32 h32 checkBlocks_94592_94655_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94656_94719_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94656_94719_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94656_94719 :
    ∀ i : Fin 64, indexedBlockCheck (94656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94656 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94656 0 32 h0 checkBlocks_94656_94719_part0
  have h64 := extendCertifiedSegment 94656 32 32 h32 checkBlocks_94656_94719_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94208_94719 :
    ∀ i : Fin 512, indexedBlockCheck (94208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94208 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 94208 0 64 h0 checkBlocks_94208_94271
  have h128 := extendCertifiedSegment 94208 64 64 h64 checkBlocks_94272_94335
  have h192 := extendCertifiedSegment 94208 128 64 h128 checkBlocks_94336_94399
  have h256 := extendCertifiedSegment 94208 192 64 h192 checkBlocks_94400_94463
  have h320 := extendCertifiedSegment 94208 256 64 h256 checkBlocks_94464_94527
  have h384 := extendCertifiedSegment 94208 320 64 h320 checkBlocks_94528_94591
  have h448 := extendCertifiedSegment 94208 384 64 h384 checkBlocks_94592_94655
  have h512 := extendCertifiedSegment 94208 448 64 h448 checkBlocks_94656_94719
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_94720_94783_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94720_94783_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94720_94783 :
    ∀ i : Fin 64, indexedBlockCheck (94720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94720 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94720 0 32 h0 checkBlocks_94720_94783_part0
  have h64 := extendCertifiedSegment 94720 32 32 h32 checkBlocks_94720_94783_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94784_94847_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94784_94847_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94784_94847 :
    ∀ i : Fin 64, indexedBlockCheck (94784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94784 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94784 0 32 h0 checkBlocks_94784_94847_part0
  have h64 := extendCertifiedSegment 94784 32 32 h32 checkBlocks_94784_94847_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94848_94911_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94848_94911_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94848_94911 :
    ∀ i : Fin 64, indexedBlockCheck (94848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94848 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94848 0 32 h0 checkBlocks_94848_94911_part0
  have h64 := extendCertifiedSegment 94848 32 32 h32 checkBlocks_94848_94911_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94912_94975_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94912_94975_part1 :
    ∀ i : Fin 32, indexedBlockCheck (94944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94912_94975 :
    ∀ i : Fin 64, indexedBlockCheck (94912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94912 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94912 0 32 h0 checkBlocks_94912_94975_part0
  have h64 := extendCertifiedSegment 94912 32 32 h32 checkBlocks_94912_94975_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94976_95039_part0 :
    ∀ i : Fin 32, indexedBlockCheck (94976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94976_95039_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94976_95039 :
    ∀ i : Fin 64, indexedBlockCheck (94976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94976 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 94976 0 32 h0 checkBlocks_94976_95039_part0
  have h64 := extendCertifiedSegment 94976 32 32 h32 checkBlocks_94976_95039_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95040_95103_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95040_95103_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95040_95103 :
    ∀ i : Fin 64, indexedBlockCheck (95040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95040 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95040 0 32 h0 checkBlocks_95040_95103_part0
  have h64 := extendCertifiedSegment 95040 32 32 h32 checkBlocks_95040_95103_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95104_95167_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95104_95167_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95104_95167 :
    ∀ i : Fin 64, indexedBlockCheck (95104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95104 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95104 0 32 h0 checkBlocks_95104_95167_part0
  have h64 := extendCertifiedSegment 95104 32 32 h32 checkBlocks_95104_95167_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_95168_95231_part0 :
    ∀ i : Fin 32, indexedBlockCheck (95168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95168_95231_part1 :
    ∀ i : Fin 32, indexedBlockCheck (95200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95168_95231 :
    ∀ i : Fin 64, indexedBlockCheck (95168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (95168 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 95168 0 32 h0 checkBlocks_95168_95231_part0
  have h64 := extendCertifiedSegment 95168 32 32 h32 checkBlocks_95168_95231_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_94720_95231 :
    ∀ i : Fin 512, indexedBlockCheck (94720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94720 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 94720 0 64 h0 checkBlocks_94720_94783
  have h128 := extendCertifiedSegment 94720 64 64 h64 checkBlocks_94784_94847
  have h192 := extendCertifiedSegment 94720 128 64 h128 checkBlocks_94848_94911
  have h256 := extendCertifiedSegment 94720 192 64 h192 checkBlocks_94912_94975
  have h320 := extendCertifiedSegment 94720 256 64 h256 checkBlocks_94976_95039
  have h384 := extendCertifiedSegment 94720 320 64 h320 checkBlocks_95040_95103
  have h448 := extendCertifiedSegment 94720 384 64 h384 checkBlocks_95104_95167
  have h512 := extendCertifiedSegment 94720 448 64 h448 checkBlocks_95168_95231
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [93184, 95232) passes the packed checker. -/
public theorem blocks_in_93184_95232 :
    ∀ i : Fin 2048, indexedBlockCheck (93184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93184 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 93184 0 512 h0 checkBlocks_93184_93695
  have h1024 := extendCertifiedSegment 93184 512 512 h512 checkBlocks_93696_94207
  have h1536 := extendCertifiedSegment 93184 1024 512 h1024 checkBlocks_94208_94719
  have h2048 := extendCertifiedSegment 93184 1536 512 h1536 checkBlocks_94720_95231
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
