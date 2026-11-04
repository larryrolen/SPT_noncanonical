/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 84992 through 87039 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_84992_85055_part0 :
    ∀ i : Fin 32, indexedBlockCheck (84992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84992_85055_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84992_85055 :
    ∀ i : Fin 64, indexedBlockCheck (84992 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84992 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 84992 0 32 h0 checkBlocks_84992_85055_part0
  have h64 := extendCertifiedSegment 84992 32 32 h32 checkBlocks_84992_85055_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85056_85119_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85056_85119_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85056_85119 :
    ∀ i : Fin 64, indexedBlockCheck (85056 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85056 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85056 0 32 h0 checkBlocks_85056_85119_part0
  have h64 := extendCertifiedSegment 85056 32 32 h32 checkBlocks_85056_85119_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85120_85183_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85120_85183_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85120_85183 :
    ∀ i : Fin 64, indexedBlockCheck (85120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85120 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85120 0 32 h0 checkBlocks_85120_85183_part0
  have h64 := extendCertifiedSegment 85120 32 32 h32 checkBlocks_85120_85183_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85184_85247_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85184_85247_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85184_85247 :
    ∀ i : Fin 64, indexedBlockCheck (85184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85184 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85184 0 32 h0 checkBlocks_85184_85247_part0
  have h64 := extendCertifiedSegment 85184 32 32 h32 checkBlocks_85184_85247_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85248_85311_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85248_85311_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85248_85311 :
    ∀ i : Fin 64, indexedBlockCheck (85248 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85248 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85248 0 32 h0 checkBlocks_85248_85311_part0
  have h64 := extendCertifiedSegment 85248 32 32 h32 checkBlocks_85248_85311_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85312_85375_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85312_85375_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85312_85375 :
    ∀ i : Fin 64, indexedBlockCheck (85312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85312 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85312 0 32 h0 checkBlocks_85312_85375_part0
  have h64 := extendCertifiedSegment 85312 32 32 h32 checkBlocks_85312_85375_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85376_85439_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85376_85439_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85376_85439 :
    ∀ i : Fin 64, indexedBlockCheck (85376 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85376 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85376 0 32 h0 checkBlocks_85376_85439_part0
  have h64 := extendCertifiedSegment 85376 32 32 h32 checkBlocks_85376_85439_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85440_85503_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85440_85503_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85440_85503 :
    ∀ i : Fin 64, indexedBlockCheck (85440 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85440 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85440 0 32 h0 checkBlocks_85440_85503_part0
  have h64 := extendCertifiedSegment 85440 32 32 h32 checkBlocks_85440_85503_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_84992_85503 :
    ∀ i : Fin 512, indexedBlockCheck (84992 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84992 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 84992 0 64 h0 checkBlocks_84992_85055
  have h128 := extendCertifiedSegment 84992 64 64 h64 checkBlocks_85056_85119
  have h192 := extendCertifiedSegment 84992 128 64 h128 checkBlocks_85120_85183
  have h256 := extendCertifiedSegment 84992 192 64 h192 checkBlocks_85184_85247
  have h320 := extendCertifiedSegment 84992 256 64 h256 checkBlocks_85248_85311
  have h384 := extendCertifiedSegment 84992 320 64 h320 checkBlocks_85312_85375
  have h448 := extendCertifiedSegment 84992 384 64 h384 checkBlocks_85376_85439
  have h512 := extendCertifiedSegment 84992 448 64 h448 checkBlocks_85440_85503
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_85504_85567_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85504_85567_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85504_85567 :
    ∀ i : Fin 64, indexedBlockCheck (85504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85504 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85504 0 32 h0 checkBlocks_85504_85567_part0
  have h64 := extendCertifiedSegment 85504 32 32 h32 checkBlocks_85504_85567_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85568_85631_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85568_85631_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85568_85631 :
    ∀ i : Fin 64, indexedBlockCheck (85568 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85568 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85568 0 32 h0 checkBlocks_85568_85631_part0
  have h64 := extendCertifiedSegment 85568 32 32 h32 checkBlocks_85568_85631_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85632_85695_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85632_85695_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85632_85695 :
    ∀ i : Fin 64, indexedBlockCheck (85632 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85632 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85632 0 32 h0 checkBlocks_85632_85695_part0
  have h64 := extendCertifiedSegment 85632 32 32 h32 checkBlocks_85632_85695_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85696_85759_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85696_85759_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85696_85759 :
    ∀ i : Fin 64, indexedBlockCheck (85696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85696 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85696 0 32 h0 checkBlocks_85696_85759_part0
  have h64 := extendCertifiedSegment 85696 32 32 h32 checkBlocks_85696_85759_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85760_85823_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85760_85823_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85760_85823 :
    ∀ i : Fin 64, indexedBlockCheck (85760 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85760 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85760 0 32 h0 checkBlocks_85760_85823_part0
  have h64 := extendCertifiedSegment 85760 32 32 h32 checkBlocks_85760_85823_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85824_85887_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85824_85887_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85824_85887 :
    ∀ i : Fin 64, indexedBlockCheck (85824 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85824 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85824 0 32 h0 checkBlocks_85824_85887_part0
  have h64 := extendCertifiedSegment 85824 32 32 h32 checkBlocks_85824_85887_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85888_85951_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85888_85951_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85888_85951 :
    ∀ i : Fin 64, indexedBlockCheck (85888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85888 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85888 0 32 h0 checkBlocks_85888_85951_part0
  have h64 := extendCertifiedSegment 85888 32 32 h32 checkBlocks_85888_85951_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85952_86015_part0 :
    ∀ i : Fin 32, indexedBlockCheck (85952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85952_86015_part1 :
    ∀ i : Fin 32, indexedBlockCheck (85984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_85952_86015 :
    ∀ i : Fin 64, indexedBlockCheck (85952 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85952 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 85952 0 32 h0 checkBlocks_85952_86015_part0
  have h64 := extendCertifiedSegment 85952 32 32 h32 checkBlocks_85952_86015_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_85504_86015 :
    ∀ i : Fin 512, indexedBlockCheck (85504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (85504 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 85504 0 64 h0 checkBlocks_85504_85567
  have h128 := extendCertifiedSegment 85504 64 64 h64 checkBlocks_85568_85631
  have h192 := extendCertifiedSegment 85504 128 64 h128 checkBlocks_85632_85695
  have h256 := extendCertifiedSegment 85504 192 64 h192 checkBlocks_85696_85759
  have h320 := extendCertifiedSegment 85504 256 64 h256 checkBlocks_85760_85823
  have h384 := extendCertifiedSegment 85504 320 64 h320 checkBlocks_85824_85887
  have h448 := extendCertifiedSegment 85504 384 64 h384 checkBlocks_85888_85951
  have h512 := extendCertifiedSegment 85504 448 64 h448 checkBlocks_85952_86015
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_86016_86079_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86016_86079_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86016_86079 :
    ∀ i : Fin 64, indexedBlockCheck (86016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86016 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86016 0 32 h0 checkBlocks_86016_86079_part0
  have h64 := extendCertifiedSegment 86016 32 32 h32 checkBlocks_86016_86079_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86080_86143_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86080_86143_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86080_86143 :
    ∀ i : Fin 64, indexedBlockCheck (86080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86080 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86080 0 32 h0 checkBlocks_86080_86143_part0
  have h64 := extendCertifiedSegment 86080 32 32 h32 checkBlocks_86080_86143_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86144_86207_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86144_86207_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86144_86207 :
    ∀ i : Fin 64, indexedBlockCheck (86144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86144 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86144 0 32 h0 checkBlocks_86144_86207_part0
  have h64 := extendCertifiedSegment 86144 32 32 h32 checkBlocks_86144_86207_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86208_86271_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86208_86271_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86208_86271 :
    ∀ i : Fin 64, indexedBlockCheck (86208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86208 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86208 0 32 h0 checkBlocks_86208_86271_part0
  have h64 := extendCertifiedSegment 86208 32 32 h32 checkBlocks_86208_86271_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86272_86335_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86272_86335_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86272_86335 :
    ∀ i : Fin 64, indexedBlockCheck (86272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86272 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86272 0 32 h0 checkBlocks_86272_86335_part0
  have h64 := extendCertifiedSegment 86272 32 32 h32 checkBlocks_86272_86335_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86336_86399_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86336_86399_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86336_86399 :
    ∀ i : Fin 64, indexedBlockCheck (86336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86336 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86336 0 32 h0 checkBlocks_86336_86399_part0
  have h64 := extendCertifiedSegment 86336 32 32 h32 checkBlocks_86336_86399_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86400_86463_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86400_86463_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86400_86463 :
    ∀ i : Fin 64, indexedBlockCheck (86400 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86400 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86400 0 32 h0 checkBlocks_86400_86463_part0
  have h64 := extendCertifiedSegment 86400 32 32 h32 checkBlocks_86400_86463_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86464_86527_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86464_86527_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86464_86527 :
    ∀ i : Fin 64, indexedBlockCheck (86464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86464 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86464 0 32 h0 checkBlocks_86464_86527_part0
  have h64 := extendCertifiedSegment 86464 32 32 h32 checkBlocks_86464_86527_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86016_86527 :
    ∀ i : Fin 512, indexedBlockCheck (86016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86016 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 86016 0 64 h0 checkBlocks_86016_86079
  have h128 := extendCertifiedSegment 86016 64 64 h64 checkBlocks_86080_86143
  have h192 := extendCertifiedSegment 86016 128 64 h128 checkBlocks_86144_86207
  have h256 := extendCertifiedSegment 86016 192 64 h192 checkBlocks_86208_86271
  have h320 := extendCertifiedSegment 86016 256 64 h256 checkBlocks_86272_86335
  have h384 := extendCertifiedSegment 86016 320 64 h320 checkBlocks_86336_86399
  have h448 := extendCertifiedSegment 86016 384 64 h384 checkBlocks_86400_86463
  have h512 := extendCertifiedSegment 86016 448 64 h448 checkBlocks_86464_86527
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_86528_86591_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86528_86591_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86528_86591 :
    ∀ i : Fin 64, indexedBlockCheck (86528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86528 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86528 0 32 h0 checkBlocks_86528_86591_part0
  have h64 := extendCertifiedSegment 86528 32 32 h32 checkBlocks_86528_86591_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86592_86655_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86592_86655_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86592_86655 :
    ∀ i : Fin 64, indexedBlockCheck (86592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86592 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86592 0 32 h0 checkBlocks_86592_86655_part0
  have h64 := extendCertifiedSegment 86592 32 32 h32 checkBlocks_86592_86655_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86656_86719_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86656_86719_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86656_86719 :
    ∀ i : Fin 64, indexedBlockCheck (86656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86656 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86656 0 32 h0 checkBlocks_86656_86719_part0
  have h64 := extendCertifiedSegment 86656 32 32 h32 checkBlocks_86656_86719_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86720_86783_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86720_86783_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86720_86783 :
    ∀ i : Fin 64, indexedBlockCheck (86720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86720 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86720 0 32 h0 checkBlocks_86720_86783_part0
  have h64 := extendCertifiedSegment 86720 32 32 h32 checkBlocks_86720_86783_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86784_86847_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86784_86847_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86784_86847 :
    ∀ i : Fin 64, indexedBlockCheck (86784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86784 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86784 0 32 h0 checkBlocks_86784_86847_part0
  have h64 := extendCertifiedSegment 86784 32 32 h32 checkBlocks_86784_86847_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86848_86911_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86848_86911_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86848_86911 :
    ∀ i : Fin 64, indexedBlockCheck (86848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86848 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86848 0 32 h0 checkBlocks_86848_86911_part0
  have h64 := extendCertifiedSegment 86848 32 32 h32 checkBlocks_86848_86911_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86912_86975_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86912_86975_part1 :
    ∀ i : Fin 32, indexedBlockCheck (86944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86912_86975 :
    ∀ i : Fin 64, indexedBlockCheck (86912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86912 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86912 0 32 h0 checkBlocks_86912_86975_part0
  have h64 := extendCertifiedSegment 86912 32 32 h32 checkBlocks_86912_86975_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86976_87039_part0 :
    ∀ i : Fin 32, indexedBlockCheck (86976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86976_87039_part1 :
    ∀ i : Fin 32, indexedBlockCheck (87008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_86976_87039 :
    ∀ i : Fin 64, indexedBlockCheck (86976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86976 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 86976 0 32 h0 checkBlocks_86976_87039_part0
  have h64 := extendCertifiedSegment 86976 32 32 h32 checkBlocks_86976_87039_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_86528_87039 :
    ∀ i : Fin 512, indexedBlockCheck (86528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (86528 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 86528 0 64 h0 checkBlocks_86528_86591
  have h128 := extendCertifiedSegment 86528 64 64 h64 checkBlocks_86592_86655
  have h192 := extendCertifiedSegment 86528 128 64 h128 checkBlocks_86656_86719
  have h256 := extendCertifiedSegment 86528 192 64 h192 checkBlocks_86720_86783
  have h320 := extendCertifiedSegment 86528 256 64 h256 checkBlocks_86784_86847
  have h384 := extendCertifiedSegment 86528 320 64 h320 checkBlocks_86848_86911
  have h448 := extendCertifiedSegment 86528 384 64 h384 checkBlocks_86912_86975
  have h512 := extendCertifiedSegment 86528 448 64 h448 checkBlocks_86976_87039
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [84992, 87040) passes the packed checker. -/
public theorem blocks_in_84992_87040 :
    ∀ i : Fin 2048, indexedBlockCheck (84992 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84992 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 84992 0 512 h0 checkBlocks_84992_85503
  have h1024 := extendCertifiedSegment 84992 512 512 h512 checkBlocks_85504_86015
  have h1536 := extendCertifiedSegment 84992 1024 512 h1024 checkBlocks_86016_86527
  have h2048 := extendCertifiedSegment 84992 1536 512 h1536 checkBlocks_86528_87039
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
