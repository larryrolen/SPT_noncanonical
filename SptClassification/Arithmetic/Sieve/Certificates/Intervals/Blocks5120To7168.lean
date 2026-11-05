/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 5120 through 7167 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_5120_5183_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5120_5183_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5120_5183 :
    ∀ i : Fin 64, indexedBlockCheck (5120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5120 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5120 0 32 h0 checkBlocks_5120_5183_part0
  have h64 := extendCertifiedSegment 5120 32 32 h32 checkBlocks_5120_5183_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5184_5247_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5184_5247_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5184_5247 :
    ∀ i : Fin 64, indexedBlockCheck (5184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5184 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5184 0 32 h0 checkBlocks_5184_5247_part0
  have h64 := extendCertifiedSegment 5184 32 32 h32 checkBlocks_5184_5247_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5248_5311_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5248_5311_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5248_5311 :
    ∀ i : Fin 64, indexedBlockCheck (5248 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5248 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5248 0 32 h0 checkBlocks_5248_5311_part0
  have h64 := extendCertifiedSegment 5248 32 32 h32 checkBlocks_5248_5311_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5312_5375_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5312_5375_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5312_5375 :
    ∀ i : Fin 64, indexedBlockCheck (5312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5312 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5312 0 32 h0 checkBlocks_5312_5375_part0
  have h64 := extendCertifiedSegment 5312 32 32 h32 checkBlocks_5312_5375_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5376_5439_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5376_5439_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5376_5439 :
    ∀ i : Fin 64, indexedBlockCheck (5376 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5376 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5376 0 32 h0 checkBlocks_5376_5439_part0
  have h64 := extendCertifiedSegment 5376 32 32 h32 checkBlocks_5376_5439_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5440_5503_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5440_5503_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5440_5503 :
    ∀ i : Fin 64, indexedBlockCheck (5440 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5440 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5440 0 32 h0 checkBlocks_5440_5503_part0
  have h64 := extendCertifiedSegment 5440 32 32 h32 checkBlocks_5440_5503_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5504_5567_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5504_5567_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5504_5567 :
    ∀ i : Fin 64, indexedBlockCheck (5504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5504 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5504 0 32 h0 checkBlocks_5504_5567_part0
  have h64 := extendCertifiedSegment 5504 32 32 h32 checkBlocks_5504_5567_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5568_5631_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5568_5631_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5568_5631 :
    ∀ i : Fin 64, indexedBlockCheck (5568 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5568 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5568 0 32 h0 checkBlocks_5568_5631_part0
  have h64 := extendCertifiedSegment 5568 32 32 h32 checkBlocks_5568_5631_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5120_5631 :
    ∀ i : Fin 512, indexedBlockCheck (5120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5120 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 5120 0 64 h0 checkBlocks_5120_5183
  have h128 := extendCertifiedSegment 5120 64 64 h64 checkBlocks_5184_5247
  have h192 := extendCertifiedSegment 5120 128 64 h128 checkBlocks_5248_5311
  have h256 := extendCertifiedSegment 5120 192 64 h192 checkBlocks_5312_5375
  have h320 := extendCertifiedSegment 5120 256 64 h256 checkBlocks_5376_5439
  have h384 := extendCertifiedSegment 5120 320 64 h320 checkBlocks_5440_5503
  have h448 := extendCertifiedSegment 5120 384 64 h384 checkBlocks_5504_5567
  have h512 := extendCertifiedSegment 5120 448 64 h448 checkBlocks_5568_5631
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_5632_5695_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5632_5695_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5632_5695 :
    ∀ i : Fin 64, indexedBlockCheck (5632 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5632 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5632 0 32 h0 checkBlocks_5632_5695_part0
  have h64 := extendCertifiedSegment 5632 32 32 h32 checkBlocks_5632_5695_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5696_5759_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5696_5759_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5696_5759 :
    ∀ i : Fin 64, indexedBlockCheck (5696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5696 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5696 0 32 h0 checkBlocks_5696_5759_part0
  have h64 := extendCertifiedSegment 5696 32 32 h32 checkBlocks_5696_5759_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5760_5823_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5760_5823_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5760_5823 :
    ∀ i : Fin 64, indexedBlockCheck (5760 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5760 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5760 0 32 h0 checkBlocks_5760_5823_part0
  have h64 := extendCertifiedSegment 5760 32 32 h32 checkBlocks_5760_5823_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5824_5887_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5824_5887_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5824_5887 :
    ∀ i : Fin 64, indexedBlockCheck (5824 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5824 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5824 0 32 h0 checkBlocks_5824_5887_part0
  have h64 := extendCertifiedSegment 5824 32 32 h32 checkBlocks_5824_5887_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5888_5951_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5888_5951_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5888_5951 :
    ∀ i : Fin 64, indexedBlockCheck (5888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5888 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5888 0 32 h0 checkBlocks_5888_5951_part0
  have h64 := extendCertifiedSegment 5888 32 32 h32 checkBlocks_5888_5951_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5952_6015_part0 :
    ∀ i : Fin 32, indexedBlockCheck (5952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5952_6015_part1 :
    ∀ i : Fin 32, indexedBlockCheck (5984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5952_6015 :
    ∀ i : Fin 64, indexedBlockCheck (5952 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5952 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 5952 0 32 h0 checkBlocks_5952_6015_part0
  have h64 := extendCertifiedSegment 5952 32 32 h32 checkBlocks_5952_6015_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6016_6079_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6016_6079_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6016_6079 :
    ∀ i : Fin 64, indexedBlockCheck (6016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6016 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6016 0 32 h0 checkBlocks_6016_6079_part0
  have h64 := extendCertifiedSegment 6016 32 32 h32 checkBlocks_6016_6079_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6080_6143_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6080_6143_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6080_6143 :
    ∀ i : Fin 64, indexedBlockCheck (6080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6080 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6080 0 32 h0 checkBlocks_6080_6143_part0
  have h64 := extendCertifiedSegment 6080 32 32 h32 checkBlocks_6080_6143_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_5632_6143 :
    ∀ i : Fin 512, indexedBlockCheck (5632 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5632 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 5632 0 64 h0 checkBlocks_5632_5695
  have h128 := extendCertifiedSegment 5632 64 64 h64 checkBlocks_5696_5759
  have h192 := extendCertifiedSegment 5632 128 64 h128 checkBlocks_5760_5823
  have h256 := extendCertifiedSegment 5632 192 64 h192 checkBlocks_5824_5887
  have h320 := extendCertifiedSegment 5632 256 64 h256 checkBlocks_5888_5951
  have h384 := extendCertifiedSegment 5632 320 64 h320 checkBlocks_5952_6015
  have h448 := extendCertifiedSegment 5632 384 64 h384 checkBlocks_6016_6079
  have h512 := extendCertifiedSegment 5632 448 64 h448 checkBlocks_6080_6143
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_6144_6207_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6144_6207_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6144_6207 :
    ∀ i : Fin 64, indexedBlockCheck (6144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6144 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6144 0 32 h0 checkBlocks_6144_6207_part0
  have h64 := extendCertifiedSegment 6144 32 32 h32 checkBlocks_6144_6207_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6208_6271_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6208_6271_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6208_6271 :
    ∀ i : Fin 64, indexedBlockCheck (6208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6208 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6208 0 32 h0 checkBlocks_6208_6271_part0
  have h64 := extendCertifiedSegment 6208 32 32 h32 checkBlocks_6208_6271_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6272_6335_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6272_6335_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6272_6335 :
    ∀ i : Fin 64, indexedBlockCheck (6272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6272 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6272 0 32 h0 checkBlocks_6272_6335_part0
  have h64 := extendCertifiedSegment 6272 32 32 h32 checkBlocks_6272_6335_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6336_6399_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6336_6399_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6336_6399 :
    ∀ i : Fin 64, indexedBlockCheck (6336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6336 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6336 0 32 h0 checkBlocks_6336_6399_part0
  have h64 := extendCertifiedSegment 6336 32 32 h32 checkBlocks_6336_6399_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6400_6463_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6400_6463_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6400_6463 :
    ∀ i : Fin 64, indexedBlockCheck (6400 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6400 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6400 0 32 h0 checkBlocks_6400_6463_part0
  have h64 := extendCertifiedSegment 6400 32 32 h32 checkBlocks_6400_6463_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6464_6527_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6464_6527_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6464_6527 :
    ∀ i : Fin 64, indexedBlockCheck (6464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6464 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6464 0 32 h0 checkBlocks_6464_6527_part0
  have h64 := extendCertifiedSegment 6464 32 32 h32 checkBlocks_6464_6527_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6528_6591_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6528_6591_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6528_6591 :
    ∀ i : Fin 64, indexedBlockCheck (6528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6528 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6528 0 32 h0 checkBlocks_6528_6591_part0
  have h64 := extendCertifiedSegment 6528 32 32 h32 checkBlocks_6528_6591_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6592_6655_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6592_6655_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6592_6655 :
    ∀ i : Fin 64, indexedBlockCheck (6592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6592 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6592 0 32 h0 checkBlocks_6592_6655_part0
  have h64 := extendCertifiedSegment 6592 32 32 h32 checkBlocks_6592_6655_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6144_6655 :
    ∀ i : Fin 512, indexedBlockCheck (6144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6144 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 6144 0 64 h0 checkBlocks_6144_6207
  have h128 := extendCertifiedSegment 6144 64 64 h64 checkBlocks_6208_6271
  have h192 := extendCertifiedSegment 6144 128 64 h128 checkBlocks_6272_6335
  have h256 := extendCertifiedSegment 6144 192 64 h192 checkBlocks_6336_6399
  have h320 := extendCertifiedSegment 6144 256 64 h256 checkBlocks_6400_6463
  have h384 := extendCertifiedSegment 6144 320 64 h320 checkBlocks_6464_6527
  have h448 := extendCertifiedSegment 6144 384 64 h384 checkBlocks_6528_6591
  have h512 := extendCertifiedSegment 6144 448 64 h448 checkBlocks_6592_6655
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_6656_6719_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6656_6719_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6656_6719 :
    ∀ i : Fin 64, indexedBlockCheck (6656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6656 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6656 0 32 h0 checkBlocks_6656_6719_part0
  have h64 := extendCertifiedSegment 6656 32 32 h32 checkBlocks_6656_6719_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6720_6783_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6720_6783_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6720_6783 :
    ∀ i : Fin 64, indexedBlockCheck (6720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6720 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6720 0 32 h0 checkBlocks_6720_6783_part0
  have h64 := extendCertifiedSegment 6720 32 32 h32 checkBlocks_6720_6783_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6784_6847_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6784_6847_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6784_6847 :
    ∀ i : Fin 64, indexedBlockCheck (6784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6784 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6784 0 32 h0 checkBlocks_6784_6847_part0
  have h64 := extendCertifiedSegment 6784 32 32 h32 checkBlocks_6784_6847_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6848_6911_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6848_6911_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6848_6911 :
    ∀ i : Fin 64, indexedBlockCheck (6848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6848 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6848 0 32 h0 checkBlocks_6848_6911_part0
  have h64 := extendCertifiedSegment 6848 32 32 h32 checkBlocks_6848_6911_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6912_6975_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6912_6975_part1 :
    ∀ i : Fin 32, indexedBlockCheck (6944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6912_6975 :
    ∀ i : Fin 64, indexedBlockCheck (6912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6912 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6912 0 32 h0 checkBlocks_6912_6975_part0
  have h64 := extendCertifiedSegment 6912 32 32 h32 checkBlocks_6912_6975_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6976_7039_part0 :
    ∀ i : Fin 32, indexedBlockCheck (6976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6976_7039_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6976_7039 :
    ∀ i : Fin 64, indexedBlockCheck (6976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6976 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 6976 0 32 h0 checkBlocks_6976_7039_part0
  have h64 := extendCertifiedSegment 6976 32 32 h32 checkBlocks_6976_7039_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7040_7103_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7040_7103_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7040_7103 :
    ∀ i : Fin 64, indexedBlockCheck (7040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7040 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7040 0 32 h0 checkBlocks_7040_7103_part0
  have h64 := extendCertifiedSegment 7040 32 32 h32 checkBlocks_7040_7103_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_7104_7167_part0 :
    ∀ i : Fin 32, indexedBlockCheck (7104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7104_7167_part1 :
    ∀ i : Fin 32, indexedBlockCheck (7136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7104_7167 :
    ∀ i : Fin 64, indexedBlockCheck (7104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (7104 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 7104 0 32 h0 checkBlocks_7104_7167_part0
  have h64 := extendCertifiedSegment 7104 32 32 h32 checkBlocks_7104_7167_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_6656_7167 :
    ∀ i : Fin 512, indexedBlockCheck (6656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (6656 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 6656 0 64 h0 checkBlocks_6656_6719
  have h128 := extendCertifiedSegment 6656 64 64 h64 checkBlocks_6720_6783
  have h192 := extendCertifiedSegment 6656 128 64 h128 checkBlocks_6784_6847
  have h256 := extendCertifiedSegment 6656 192 64 h192 checkBlocks_6848_6911
  have h320 := extendCertifiedSegment 6656 256 64 h256 checkBlocks_6912_6975
  have h384 := extendCertifiedSegment 6656 320 64 h320 checkBlocks_6976_7039
  have h448 := extendCertifiedSegment 6656 384 64 h384 checkBlocks_7040_7103
  have h512 := extendCertifiedSegment 6656 448 64 h448 checkBlocks_7104_7167
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [5120, 7168) passes the packed checker. -/
public theorem blocks_in_5120_7168 :
    ∀ i : Fin 2048, indexedBlockCheck (5120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (5120 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 5120 0 512 h0 checkBlocks_5120_5631
  have h1024 := extendCertifiedSegment 5120 512 512 h512 checkBlocks_5632_6143
  have h1536 := extendCertifiedSegment 5120 1024 512 h1024 checkBlocks_6144_6655
  have h2048 := extendCertifiedSegment 5120 1536 512 h1536 checkBlocks_6656_7167
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
