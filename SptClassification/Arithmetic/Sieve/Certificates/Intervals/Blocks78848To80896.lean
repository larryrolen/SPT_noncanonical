/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 78848 through 80895 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_78848_78911_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78848_78911_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78848_78911 :
    ∀ i : Fin 64, indexedBlockCheck (78848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78848 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78848 0 32 h0 checkBlocks_78848_78911_part0
  have h64 := extendCertifiedSegment 78848 32 32 h32 checkBlocks_78848_78911_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78912_78975_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78912_78975_part1 :
    ∀ i : Fin 32, indexedBlockCheck (78944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78912_78975 :
    ∀ i : Fin 64, indexedBlockCheck (78912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78912 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78912 0 32 h0 checkBlocks_78912_78975_part0
  have h64 := extendCertifiedSegment 78912 32 32 h32 checkBlocks_78912_78975_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78976_79039_part0 :
    ∀ i : Fin 32, indexedBlockCheck (78976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78976_79039_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_78976_79039 :
    ∀ i : Fin 64, indexedBlockCheck (78976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78976 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 78976 0 32 h0 checkBlocks_78976_79039_part0
  have h64 := extendCertifiedSegment 78976 32 32 h32 checkBlocks_78976_79039_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79040_79103_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79040_79103_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79040_79103 :
    ∀ i : Fin 64, indexedBlockCheck (79040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79040 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79040 0 32 h0 checkBlocks_79040_79103_part0
  have h64 := extendCertifiedSegment 79040 32 32 h32 checkBlocks_79040_79103_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79104_79167_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79104_79167_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79104_79167 :
    ∀ i : Fin 64, indexedBlockCheck (79104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79104 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79104 0 32 h0 checkBlocks_79104_79167_part0
  have h64 := extendCertifiedSegment 79104 32 32 h32 checkBlocks_79104_79167_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79168_79231_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79168_79231_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79168_79231 :
    ∀ i : Fin 64, indexedBlockCheck (79168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79168 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79168 0 32 h0 checkBlocks_79168_79231_part0
  have h64 := extendCertifiedSegment 79168 32 32 h32 checkBlocks_79168_79231_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79232_79295_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79232_79295_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79232_79295 :
    ∀ i : Fin 64, indexedBlockCheck (79232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79232 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79232 0 32 h0 checkBlocks_79232_79295_part0
  have h64 := extendCertifiedSegment 79232 32 32 h32 checkBlocks_79232_79295_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79296_79359_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79296_79359_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79296_79359 :
    ∀ i : Fin 64, indexedBlockCheck (79296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79296 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79296 0 32 h0 checkBlocks_79296_79359_part0
  have h64 := extendCertifiedSegment 79296 32 32 h32 checkBlocks_79296_79359_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_78848_79359 :
    ∀ i : Fin 512, indexedBlockCheck (78848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78848 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 78848 0 64 h0 checkBlocks_78848_78911
  have h128 := extendCertifiedSegment 78848 64 64 h64 checkBlocks_78912_78975
  have h192 := extendCertifiedSegment 78848 128 64 h128 checkBlocks_78976_79039
  have h256 := extendCertifiedSegment 78848 192 64 h192 checkBlocks_79040_79103
  have h320 := extendCertifiedSegment 78848 256 64 h256 checkBlocks_79104_79167
  have h384 := extendCertifiedSegment 78848 320 64 h320 checkBlocks_79168_79231
  have h448 := extendCertifiedSegment 78848 384 64 h384 checkBlocks_79232_79295
  have h512 := extendCertifiedSegment 78848 448 64 h448 checkBlocks_79296_79359
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_79360_79423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79360_79423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79360_79423 :
    ∀ i : Fin 64, indexedBlockCheck (79360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79360 0 32 h0 checkBlocks_79360_79423_part0
  have h64 := extendCertifiedSegment 79360 32 32 h32 checkBlocks_79360_79423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79424_79487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79424_79487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79424_79487 :
    ∀ i : Fin 64, indexedBlockCheck (79424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79424 0 32 h0 checkBlocks_79424_79487_part0
  have h64 := extendCertifiedSegment 79424 32 32 h32 checkBlocks_79424_79487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79488_79551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79488_79551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79488_79551 :
    ∀ i : Fin 64, indexedBlockCheck (79488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79488 0 32 h0 checkBlocks_79488_79551_part0
  have h64 := extendCertifiedSegment 79488 32 32 h32 checkBlocks_79488_79551_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79552_79615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79552_79615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79552_79615 :
    ∀ i : Fin 64, indexedBlockCheck (79552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79552 0 32 h0 checkBlocks_79552_79615_part0
  have h64 := extendCertifiedSegment 79552 32 32 h32 checkBlocks_79552_79615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79616_79679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79616_79679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79616_79679 :
    ∀ i : Fin 64, indexedBlockCheck (79616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79616 0 32 h0 checkBlocks_79616_79679_part0
  have h64 := extendCertifiedSegment 79616 32 32 h32 checkBlocks_79616_79679_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79680_79743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79680_79743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79680_79743 :
    ∀ i : Fin 64, indexedBlockCheck (79680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79680 0 32 h0 checkBlocks_79680_79743_part0
  have h64 := extendCertifiedSegment 79680 32 32 h32 checkBlocks_79680_79743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79744_79807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79744_79807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79744_79807 :
    ∀ i : Fin 64, indexedBlockCheck (79744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79744 0 32 h0 checkBlocks_79744_79807_part0
  have h64 := extendCertifiedSegment 79744 32 32 h32 checkBlocks_79744_79807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79808_79871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79808_79871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79808_79871 :
    ∀ i : Fin 64, indexedBlockCheck (79808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79808 0 32 h0 checkBlocks_79808_79871_part0
  have h64 := extendCertifiedSegment 79808 32 32 h32 checkBlocks_79808_79871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79360_79871 :
    ∀ i : Fin 512, indexedBlockCheck (79360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79360 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 79360 0 64 h0 checkBlocks_79360_79423
  have h128 := extendCertifiedSegment 79360 64 64 h64 checkBlocks_79424_79487
  have h192 := extendCertifiedSegment 79360 128 64 h128 checkBlocks_79488_79551
  have h256 := extendCertifiedSegment 79360 192 64 h192 checkBlocks_79552_79615
  have h320 := extendCertifiedSegment 79360 256 64 h256 checkBlocks_79616_79679
  have h384 := extendCertifiedSegment 79360 320 64 h320 checkBlocks_79680_79743
  have h448 := extendCertifiedSegment 79360 384 64 h384 checkBlocks_79744_79807
  have h512 := extendCertifiedSegment 79360 448 64 h448 checkBlocks_79808_79871
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_79872_79935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79872_79935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79872_79935 :
    ∀ i : Fin 64, indexedBlockCheck (79872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79872 0 32 h0 checkBlocks_79872_79935_part0
  have h64 := extendCertifiedSegment 79872 32 32 h32 checkBlocks_79872_79935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79936_79999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (79936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79936_79999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (79968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_79936_79999 :
    ∀ i : Fin 64, indexedBlockCheck (79936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 79936 0 32 h0 checkBlocks_79936_79999_part0
  have h64 := extendCertifiedSegment 79936 32 32 h32 checkBlocks_79936_79999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80000_80063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80000_80063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80000_80063 :
    ∀ i : Fin 64, indexedBlockCheck (80000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80000 0 32 h0 checkBlocks_80000_80063_part0
  have h64 := extendCertifiedSegment 80000 32 32 h32 checkBlocks_80000_80063_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80064_80127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80064_80127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80064_80127 :
    ∀ i : Fin 64, indexedBlockCheck (80064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80064 0 32 h0 checkBlocks_80064_80127_part0
  have h64 := extendCertifiedSegment 80064 32 32 h32 checkBlocks_80064_80127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80128_80191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80128_80191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80128_80191 :
    ∀ i : Fin 64, indexedBlockCheck (80128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80128 0 32 h0 checkBlocks_80128_80191_part0
  have h64 := extendCertifiedSegment 80128 32 32 h32 checkBlocks_80128_80191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80192_80255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80192_80255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80192_80255 :
    ∀ i : Fin 64, indexedBlockCheck (80192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80192 0 32 h0 checkBlocks_80192_80255_part0
  have h64 := extendCertifiedSegment 80192 32 32 h32 checkBlocks_80192_80255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80256_80319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80256_80319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80256_80319 :
    ∀ i : Fin 64, indexedBlockCheck (80256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80256 0 32 h0 checkBlocks_80256_80319_part0
  have h64 := extendCertifiedSegment 80256 32 32 h32 checkBlocks_80256_80319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80320_80383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80320_80383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80320_80383 :
    ∀ i : Fin 64, indexedBlockCheck (80320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80320 0 32 h0 checkBlocks_80320_80383_part0
  have h64 := extendCertifiedSegment 80320 32 32 h32 checkBlocks_80320_80383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_79872_80383 :
    ∀ i : Fin 512, indexedBlockCheck (79872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (79872 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 79872 0 64 h0 checkBlocks_79872_79935
  have h128 := extendCertifiedSegment 79872 64 64 h64 checkBlocks_79936_79999
  have h192 := extendCertifiedSegment 79872 128 64 h128 checkBlocks_80000_80063
  have h256 := extendCertifiedSegment 79872 192 64 h192 checkBlocks_80064_80127
  have h320 := extendCertifiedSegment 79872 256 64 h256 checkBlocks_80128_80191
  have h384 := extendCertifiedSegment 79872 320 64 h320 checkBlocks_80192_80255
  have h448 := extendCertifiedSegment 79872 384 64 h384 checkBlocks_80256_80319
  have h512 := extendCertifiedSegment 79872 448 64 h448 checkBlocks_80320_80383
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_80384_80447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80384_80447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80384_80447 :
    ∀ i : Fin 64, indexedBlockCheck (80384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80384 0 32 h0 checkBlocks_80384_80447_part0
  have h64 := extendCertifiedSegment 80384 32 32 h32 checkBlocks_80384_80447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80448_80511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80448_80511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80448_80511 :
    ∀ i : Fin 64, indexedBlockCheck (80448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80448 0 32 h0 checkBlocks_80448_80511_part0
  have h64 := extendCertifiedSegment 80448 32 32 h32 checkBlocks_80448_80511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80512_80575_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80512_80575_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80512_80575 :
    ∀ i : Fin 64, indexedBlockCheck (80512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80512 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80512 0 32 h0 checkBlocks_80512_80575_part0
  have h64 := extendCertifiedSegment 80512 32 32 h32 checkBlocks_80512_80575_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80576_80639_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80576_80639_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80576_80639 :
    ∀ i : Fin 64, indexedBlockCheck (80576 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80576 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80576 0 32 h0 checkBlocks_80576_80639_part0
  have h64 := extendCertifiedSegment 80576 32 32 h32 checkBlocks_80576_80639_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80640_80703_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80640_80703_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80640_80703 :
    ∀ i : Fin 64, indexedBlockCheck (80640 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80640 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80640 0 32 h0 checkBlocks_80640_80703_part0
  have h64 := extendCertifiedSegment 80640 32 32 h32 checkBlocks_80640_80703_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80704_80767_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80704_80767_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80704_80767 :
    ∀ i : Fin 64, indexedBlockCheck (80704 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80704 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80704 0 32 h0 checkBlocks_80704_80767_part0
  have h64 := extendCertifiedSegment 80704 32 32 h32 checkBlocks_80704_80767_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80768_80831_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80768_80831_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80768_80831 :
    ∀ i : Fin 64, indexedBlockCheck (80768 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80768 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80768 0 32 h0 checkBlocks_80768_80831_part0
  have h64 := extendCertifiedSegment 80768 32 32 h32 checkBlocks_80768_80831_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80832_80895_part0 :
    ∀ i : Fin 32, indexedBlockCheck (80832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80832_80895_part1 :
    ∀ i : Fin 32, indexedBlockCheck (80864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_80832_80895 :
    ∀ i : Fin 64, indexedBlockCheck (80832 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80832 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 80832 0 32 h0 checkBlocks_80832_80895_part0
  have h64 := extendCertifiedSegment 80832 32 32 h32 checkBlocks_80832_80895_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_80384_80895 :
    ∀ i : Fin 512, indexedBlockCheck (80384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (80384 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 80384 0 64 h0 checkBlocks_80384_80447
  have h128 := extendCertifiedSegment 80384 64 64 h64 checkBlocks_80448_80511
  have h192 := extendCertifiedSegment 80384 128 64 h128 checkBlocks_80512_80575
  have h256 := extendCertifiedSegment 80384 192 64 h192 checkBlocks_80576_80639
  have h320 := extendCertifiedSegment 80384 256 64 h256 checkBlocks_80640_80703
  have h384 := extendCertifiedSegment 80384 320 64 h320 checkBlocks_80704_80767
  have h448 := extendCertifiedSegment 80384 384 64 h384 checkBlocks_80768_80831
  have h512 := extendCertifiedSegment 80384 448 64 h448 checkBlocks_80832_80895
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [78848, 80896) passes the packed checker. -/
public theorem blocks_in_78848_80896 :
    ∀ i : Fin 2048, indexedBlockCheck (78848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (78848 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 78848 0 512 h0 checkBlocks_78848_79359
  have h1024 := extendCertifiedSegment 78848 512 512 h512 checkBlocks_79360_79871
  have h1536 := extendCertifiedSegment 78848 1024 512 h1024 checkBlocks_79872_80383
  have h2048 := extendCertifiedSegment 78848 1536 512 h1536 checkBlocks_80384_80895
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
