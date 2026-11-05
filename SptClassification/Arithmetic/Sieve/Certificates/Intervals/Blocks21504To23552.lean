/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 21504 through 23551 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_21504_21567_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21504_21567_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21504_21567 :
    ∀ i : Fin 64, indexedBlockCheck (21504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21504 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21504 0 32 h0 checkBlocks_21504_21567_part0
  have h64 := extendCertifiedSegment 21504 32 32 h32 checkBlocks_21504_21567_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21568_21631_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21568_21631_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21568_21631 :
    ∀ i : Fin 64, indexedBlockCheck (21568 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21568 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21568 0 32 h0 checkBlocks_21568_21631_part0
  have h64 := extendCertifiedSegment 21568 32 32 h32 checkBlocks_21568_21631_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21632_21695_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21632_21695_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21632_21695 :
    ∀ i : Fin 64, indexedBlockCheck (21632 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21632 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21632 0 32 h0 checkBlocks_21632_21695_part0
  have h64 := extendCertifiedSegment 21632 32 32 h32 checkBlocks_21632_21695_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21696_21759_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21696_21759_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21696_21759 :
    ∀ i : Fin 64, indexedBlockCheck (21696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21696 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21696 0 32 h0 checkBlocks_21696_21759_part0
  have h64 := extendCertifiedSegment 21696 32 32 h32 checkBlocks_21696_21759_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21760_21823_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21760_21823_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21760_21823 :
    ∀ i : Fin 64, indexedBlockCheck (21760 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21760 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21760 0 32 h0 checkBlocks_21760_21823_part0
  have h64 := extendCertifiedSegment 21760 32 32 h32 checkBlocks_21760_21823_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21824_21887_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21824_21887_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21824_21887 :
    ∀ i : Fin 64, indexedBlockCheck (21824 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21824 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21824 0 32 h0 checkBlocks_21824_21887_part0
  have h64 := extendCertifiedSegment 21824 32 32 h32 checkBlocks_21824_21887_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21888_21951_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21888_21951_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21888_21951 :
    ∀ i : Fin 64, indexedBlockCheck (21888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21888 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21888 0 32 h0 checkBlocks_21888_21951_part0
  have h64 := extendCertifiedSegment 21888 32 32 h32 checkBlocks_21888_21951_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21952_22015_part0 :
    ∀ i : Fin 32, indexedBlockCheck (21952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21952_22015_part1 :
    ∀ i : Fin 32, indexedBlockCheck (21984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_21952_22015 :
    ∀ i : Fin 64, indexedBlockCheck (21952 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21952 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 21952 0 32 h0 checkBlocks_21952_22015_part0
  have h64 := extendCertifiedSegment 21952 32 32 h32 checkBlocks_21952_22015_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_21504_22015 :
    ∀ i : Fin 512, indexedBlockCheck (21504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21504 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 21504 0 64 h0 checkBlocks_21504_21567
  have h128 := extendCertifiedSegment 21504 64 64 h64 checkBlocks_21568_21631
  have h192 := extendCertifiedSegment 21504 128 64 h128 checkBlocks_21632_21695
  have h256 := extendCertifiedSegment 21504 192 64 h192 checkBlocks_21696_21759
  have h320 := extendCertifiedSegment 21504 256 64 h256 checkBlocks_21760_21823
  have h384 := extendCertifiedSegment 21504 320 64 h320 checkBlocks_21824_21887
  have h448 := extendCertifiedSegment 21504 384 64 h384 checkBlocks_21888_21951
  have h512 := extendCertifiedSegment 21504 448 64 h448 checkBlocks_21952_22015
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_22016_22079_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22016_22079_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22016_22079 :
    ∀ i : Fin 64, indexedBlockCheck (22016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22016 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22016 0 32 h0 checkBlocks_22016_22079_part0
  have h64 := extendCertifiedSegment 22016 32 32 h32 checkBlocks_22016_22079_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22080_22143_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22080_22143_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22080_22143 :
    ∀ i : Fin 64, indexedBlockCheck (22080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22080 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22080 0 32 h0 checkBlocks_22080_22143_part0
  have h64 := extendCertifiedSegment 22080 32 32 h32 checkBlocks_22080_22143_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22144_22207_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22144_22207_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22144_22207 :
    ∀ i : Fin 64, indexedBlockCheck (22144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22144 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22144 0 32 h0 checkBlocks_22144_22207_part0
  have h64 := extendCertifiedSegment 22144 32 32 h32 checkBlocks_22144_22207_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22208_22271_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22208_22271_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22208_22271 :
    ∀ i : Fin 64, indexedBlockCheck (22208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22208 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22208 0 32 h0 checkBlocks_22208_22271_part0
  have h64 := extendCertifiedSegment 22208 32 32 h32 checkBlocks_22208_22271_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22272_22335_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22272_22335_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22272_22335 :
    ∀ i : Fin 64, indexedBlockCheck (22272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22272 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22272 0 32 h0 checkBlocks_22272_22335_part0
  have h64 := extendCertifiedSegment 22272 32 32 h32 checkBlocks_22272_22335_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22336_22399_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22336_22399_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22336_22399 :
    ∀ i : Fin 64, indexedBlockCheck (22336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22336 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22336 0 32 h0 checkBlocks_22336_22399_part0
  have h64 := extendCertifiedSegment 22336 32 32 h32 checkBlocks_22336_22399_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22400_22463_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22400_22463_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22400_22463 :
    ∀ i : Fin 64, indexedBlockCheck (22400 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22400 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22400 0 32 h0 checkBlocks_22400_22463_part0
  have h64 := extendCertifiedSegment 22400 32 32 h32 checkBlocks_22400_22463_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22464_22527_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22464_22527_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22464_22527 :
    ∀ i : Fin 64, indexedBlockCheck (22464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22464 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22464 0 32 h0 checkBlocks_22464_22527_part0
  have h64 := extendCertifiedSegment 22464 32 32 h32 checkBlocks_22464_22527_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22016_22527 :
    ∀ i : Fin 512, indexedBlockCheck (22016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22016 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 22016 0 64 h0 checkBlocks_22016_22079
  have h128 := extendCertifiedSegment 22016 64 64 h64 checkBlocks_22080_22143
  have h192 := extendCertifiedSegment 22016 128 64 h128 checkBlocks_22144_22207
  have h256 := extendCertifiedSegment 22016 192 64 h192 checkBlocks_22208_22271
  have h320 := extendCertifiedSegment 22016 256 64 h256 checkBlocks_22272_22335
  have h384 := extendCertifiedSegment 22016 320 64 h320 checkBlocks_22336_22399
  have h448 := extendCertifiedSegment 22016 384 64 h384 checkBlocks_22400_22463
  have h512 := extendCertifiedSegment 22016 448 64 h448 checkBlocks_22464_22527
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_22528_22591_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22528_22591_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22528_22591 :
    ∀ i : Fin 64, indexedBlockCheck (22528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22528 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22528 0 32 h0 checkBlocks_22528_22591_part0
  have h64 := extendCertifiedSegment 22528 32 32 h32 checkBlocks_22528_22591_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22592_22655_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22592_22655_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22592_22655 :
    ∀ i : Fin 64, indexedBlockCheck (22592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22592 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22592 0 32 h0 checkBlocks_22592_22655_part0
  have h64 := extendCertifiedSegment 22592 32 32 h32 checkBlocks_22592_22655_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22656_22719_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22656_22719_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22656_22719 :
    ∀ i : Fin 64, indexedBlockCheck (22656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22656 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22656 0 32 h0 checkBlocks_22656_22719_part0
  have h64 := extendCertifiedSegment 22656 32 32 h32 checkBlocks_22656_22719_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22720_22783_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22720_22783_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22720_22783 :
    ∀ i : Fin 64, indexedBlockCheck (22720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22720 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22720 0 32 h0 checkBlocks_22720_22783_part0
  have h64 := extendCertifiedSegment 22720 32 32 h32 checkBlocks_22720_22783_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22784_22847_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22784_22847_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22784_22847 :
    ∀ i : Fin 64, indexedBlockCheck (22784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22784 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22784 0 32 h0 checkBlocks_22784_22847_part0
  have h64 := extendCertifiedSegment 22784 32 32 h32 checkBlocks_22784_22847_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22848_22911_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22848_22911_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22848_22911 :
    ∀ i : Fin 64, indexedBlockCheck (22848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22848 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22848 0 32 h0 checkBlocks_22848_22911_part0
  have h64 := extendCertifiedSegment 22848 32 32 h32 checkBlocks_22848_22911_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22912_22975_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22912_22975_part1 :
    ∀ i : Fin 32, indexedBlockCheck (22944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22912_22975 :
    ∀ i : Fin 64, indexedBlockCheck (22912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22912 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22912 0 32 h0 checkBlocks_22912_22975_part0
  have h64 := extendCertifiedSegment 22912 32 32 h32 checkBlocks_22912_22975_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22976_23039_part0 :
    ∀ i : Fin 32, indexedBlockCheck (22976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22976_23039_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_22976_23039 :
    ∀ i : Fin 64, indexedBlockCheck (22976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22976 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 22976 0 32 h0 checkBlocks_22976_23039_part0
  have h64 := extendCertifiedSegment 22976 32 32 h32 checkBlocks_22976_23039_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_22528_23039 :
    ∀ i : Fin 512, indexedBlockCheck (22528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (22528 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 22528 0 64 h0 checkBlocks_22528_22591
  have h128 := extendCertifiedSegment 22528 64 64 h64 checkBlocks_22592_22655
  have h192 := extendCertifiedSegment 22528 128 64 h128 checkBlocks_22656_22719
  have h256 := extendCertifiedSegment 22528 192 64 h192 checkBlocks_22720_22783
  have h320 := extendCertifiedSegment 22528 256 64 h256 checkBlocks_22784_22847
  have h384 := extendCertifiedSegment 22528 320 64 h320 checkBlocks_22848_22911
  have h448 := extendCertifiedSegment 22528 384 64 h384 checkBlocks_22912_22975
  have h512 := extendCertifiedSegment 22528 448 64 h448 checkBlocks_22976_23039
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_23040_23103_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23040_23103_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23040_23103 :
    ∀ i : Fin 64, indexedBlockCheck (23040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23040 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23040 0 32 h0 checkBlocks_23040_23103_part0
  have h64 := extendCertifiedSegment 23040 32 32 h32 checkBlocks_23040_23103_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23104_23167_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23104_23167_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23104_23167 :
    ∀ i : Fin 64, indexedBlockCheck (23104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23104 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23104 0 32 h0 checkBlocks_23104_23167_part0
  have h64 := extendCertifiedSegment 23104 32 32 h32 checkBlocks_23104_23167_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23168_23231_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23168_23231_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23168_23231 :
    ∀ i : Fin 64, indexedBlockCheck (23168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23168 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23168 0 32 h0 checkBlocks_23168_23231_part0
  have h64 := extendCertifiedSegment 23168 32 32 h32 checkBlocks_23168_23231_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23232_23295_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23232_23295_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23232_23295 :
    ∀ i : Fin 64, indexedBlockCheck (23232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23232 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23232 0 32 h0 checkBlocks_23232_23295_part0
  have h64 := extendCertifiedSegment 23232 32 32 h32 checkBlocks_23232_23295_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23296_23359_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23296_23359_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23296_23359 :
    ∀ i : Fin 64, indexedBlockCheck (23296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23296 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23296 0 32 h0 checkBlocks_23296_23359_part0
  have h64 := extendCertifiedSegment 23296 32 32 h32 checkBlocks_23296_23359_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23360_23423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23360_23423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23360_23423 :
    ∀ i : Fin 64, indexedBlockCheck (23360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23360 0 32 h0 checkBlocks_23360_23423_part0
  have h64 := extendCertifiedSegment 23360 32 32 h32 checkBlocks_23360_23423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23424_23487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23424_23487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23424_23487 :
    ∀ i : Fin 64, indexedBlockCheck (23424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23424 0 32 h0 checkBlocks_23424_23487_part0
  have h64 := extendCertifiedSegment 23424 32 32 h32 checkBlocks_23424_23487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23488_23551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (23488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23488_23551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (23520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_23488_23551 :
    ∀ i : Fin 64, indexedBlockCheck (23488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 23488 0 32 h0 checkBlocks_23488_23551_part0
  have h64 := extendCertifiedSegment 23488 32 32 h32 checkBlocks_23488_23551_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_23040_23551 :
    ∀ i : Fin 512, indexedBlockCheck (23040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (23040 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 23040 0 64 h0 checkBlocks_23040_23103
  have h128 := extendCertifiedSegment 23040 64 64 h64 checkBlocks_23104_23167
  have h192 := extendCertifiedSegment 23040 128 64 h128 checkBlocks_23168_23231
  have h256 := extendCertifiedSegment 23040 192 64 h192 checkBlocks_23232_23295
  have h320 := extendCertifiedSegment 23040 256 64 h256 checkBlocks_23296_23359
  have h384 := extendCertifiedSegment 23040 320 64 h320 checkBlocks_23360_23423
  have h448 := extendCertifiedSegment 23040 384 64 h384 checkBlocks_23424_23487
  have h512 := extendCertifiedSegment 23040 448 64 h448 checkBlocks_23488_23551
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [21504, 23552) passes the packed checker. -/
public theorem blocks_in_21504_23552 :
    ∀ i : Fin 2048, indexedBlockCheck (21504 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (21504 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 21504 0 512 h0 checkBlocks_21504_22015
  have h1024 := extendCertifiedSegment 21504 512 512 h512 checkBlocks_22016_22527
  have h1536 := extendCertifiedSegment 21504 1024 512 h1024 checkBlocks_22528_23039
  have h2048 := extendCertifiedSegment 21504 1536 512 h1536 checkBlocks_23040_23551
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
