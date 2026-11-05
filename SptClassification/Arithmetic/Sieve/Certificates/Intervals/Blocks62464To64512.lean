/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 62464 through 64511 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_62464_62527_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62464_62527_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62464_62527 :
    ∀ i : Fin 64, indexedBlockCheck (62464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62464 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62464 0 32 h0 checkBlocks_62464_62527_part0
  have h64 := extendCertifiedSegment 62464 32 32 h32 checkBlocks_62464_62527_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62528_62591_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62528_62591_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62528_62591 :
    ∀ i : Fin 64, indexedBlockCheck (62528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62528 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62528 0 32 h0 checkBlocks_62528_62591_part0
  have h64 := extendCertifiedSegment 62528 32 32 h32 checkBlocks_62528_62591_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62592_62655_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62592_62655_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62592_62655 :
    ∀ i : Fin 64, indexedBlockCheck (62592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62592 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62592 0 32 h0 checkBlocks_62592_62655_part0
  have h64 := extendCertifiedSegment 62592 32 32 h32 checkBlocks_62592_62655_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62656_62719_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62656_62719_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62656_62719 :
    ∀ i : Fin 64, indexedBlockCheck (62656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62656 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62656 0 32 h0 checkBlocks_62656_62719_part0
  have h64 := extendCertifiedSegment 62656 32 32 h32 checkBlocks_62656_62719_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62720_62783_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62720_62783_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62720_62783 :
    ∀ i : Fin 64, indexedBlockCheck (62720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62720 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62720 0 32 h0 checkBlocks_62720_62783_part0
  have h64 := extendCertifiedSegment 62720 32 32 h32 checkBlocks_62720_62783_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62784_62847_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62784_62847_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62784_62847 :
    ∀ i : Fin 64, indexedBlockCheck (62784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62784 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62784 0 32 h0 checkBlocks_62784_62847_part0
  have h64 := extendCertifiedSegment 62784 32 32 h32 checkBlocks_62784_62847_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62848_62911_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62848_62911_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62848_62911 :
    ∀ i : Fin 64, indexedBlockCheck (62848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62848 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62848 0 32 h0 checkBlocks_62848_62911_part0
  have h64 := extendCertifiedSegment 62848 32 32 h32 checkBlocks_62848_62911_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62912_62975_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62912_62975_part1 :
    ∀ i : Fin 32, indexedBlockCheck (62944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62912_62975 :
    ∀ i : Fin 64, indexedBlockCheck (62912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62912 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62912 0 32 h0 checkBlocks_62912_62975_part0
  have h64 := extendCertifiedSegment 62912 32 32 h32 checkBlocks_62912_62975_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62464_62975 :
    ∀ i : Fin 512, indexedBlockCheck (62464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62464 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 62464 0 64 h0 checkBlocks_62464_62527
  have h128 := extendCertifiedSegment 62464 64 64 h64 checkBlocks_62528_62591
  have h192 := extendCertifiedSegment 62464 128 64 h128 checkBlocks_62592_62655
  have h256 := extendCertifiedSegment 62464 192 64 h192 checkBlocks_62656_62719
  have h320 := extendCertifiedSegment 62464 256 64 h256 checkBlocks_62720_62783
  have h384 := extendCertifiedSegment 62464 320 64 h320 checkBlocks_62784_62847
  have h448 := extendCertifiedSegment 62464 384 64 h384 checkBlocks_62848_62911
  have h512 := extendCertifiedSegment 62464 448 64 h448 checkBlocks_62912_62975
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_62976_63039_part0 :
    ∀ i : Fin 32, indexedBlockCheck (62976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62976_63039_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_62976_63039 :
    ∀ i : Fin 64, indexedBlockCheck (62976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62976 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 62976 0 32 h0 checkBlocks_62976_63039_part0
  have h64 := extendCertifiedSegment 62976 32 32 h32 checkBlocks_62976_63039_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63040_63103_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63040_63103_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63040_63103 :
    ∀ i : Fin 64, indexedBlockCheck (63040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63040 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63040 0 32 h0 checkBlocks_63040_63103_part0
  have h64 := extendCertifiedSegment 63040 32 32 h32 checkBlocks_63040_63103_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63104_63167_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63104_63167_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63104_63167 :
    ∀ i : Fin 64, indexedBlockCheck (63104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63104 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63104 0 32 h0 checkBlocks_63104_63167_part0
  have h64 := extendCertifiedSegment 63104 32 32 h32 checkBlocks_63104_63167_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63168_63231_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63168_63231_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63168_63231 :
    ∀ i : Fin 64, indexedBlockCheck (63168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63168 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63168 0 32 h0 checkBlocks_63168_63231_part0
  have h64 := extendCertifiedSegment 63168 32 32 h32 checkBlocks_63168_63231_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63232_63295_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63232_63295_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63232_63295 :
    ∀ i : Fin 64, indexedBlockCheck (63232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63232 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63232 0 32 h0 checkBlocks_63232_63295_part0
  have h64 := extendCertifiedSegment 63232 32 32 h32 checkBlocks_63232_63295_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63296_63359_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63296_63359_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63296_63359 :
    ∀ i : Fin 64, indexedBlockCheck (63296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63296 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63296 0 32 h0 checkBlocks_63296_63359_part0
  have h64 := extendCertifiedSegment 63296 32 32 h32 checkBlocks_63296_63359_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63360_63423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63360_63423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63360_63423 :
    ∀ i : Fin 64, indexedBlockCheck (63360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63360 0 32 h0 checkBlocks_63360_63423_part0
  have h64 := extendCertifiedSegment 63360 32 32 h32 checkBlocks_63360_63423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63424_63487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63424_63487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63424_63487 :
    ∀ i : Fin 64, indexedBlockCheck (63424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63424 0 32 h0 checkBlocks_63424_63487_part0
  have h64 := extendCertifiedSegment 63424 32 32 h32 checkBlocks_63424_63487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_62976_63487 :
    ∀ i : Fin 512, indexedBlockCheck (62976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62976 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 62976 0 64 h0 checkBlocks_62976_63039
  have h128 := extendCertifiedSegment 62976 64 64 h64 checkBlocks_63040_63103
  have h192 := extendCertifiedSegment 62976 128 64 h128 checkBlocks_63104_63167
  have h256 := extendCertifiedSegment 62976 192 64 h192 checkBlocks_63168_63231
  have h320 := extendCertifiedSegment 62976 256 64 h256 checkBlocks_63232_63295
  have h384 := extendCertifiedSegment 62976 320 64 h320 checkBlocks_63296_63359
  have h448 := extendCertifiedSegment 62976 384 64 h384 checkBlocks_63360_63423
  have h512 := extendCertifiedSegment 62976 448 64 h448 checkBlocks_63424_63487
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_63488_63551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63488_63551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63488_63551 :
    ∀ i : Fin 64, indexedBlockCheck (63488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63488 0 32 h0 checkBlocks_63488_63551_part0
  have h64 := extendCertifiedSegment 63488 32 32 h32 checkBlocks_63488_63551_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63552_63615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63552_63615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63552_63615 :
    ∀ i : Fin 64, indexedBlockCheck (63552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63552 0 32 h0 checkBlocks_63552_63615_part0
  have h64 := extendCertifiedSegment 63552 32 32 h32 checkBlocks_63552_63615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63616_63679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63616_63679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63616_63679 :
    ∀ i : Fin 64, indexedBlockCheck (63616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63616 0 32 h0 checkBlocks_63616_63679_part0
  have h64 := extendCertifiedSegment 63616 32 32 h32 checkBlocks_63616_63679_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63680_63743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63680_63743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63680_63743 :
    ∀ i : Fin 64, indexedBlockCheck (63680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63680 0 32 h0 checkBlocks_63680_63743_part0
  have h64 := extendCertifiedSegment 63680 32 32 h32 checkBlocks_63680_63743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63744_63807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63744_63807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63744_63807 :
    ∀ i : Fin 64, indexedBlockCheck (63744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63744 0 32 h0 checkBlocks_63744_63807_part0
  have h64 := extendCertifiedSegment 63744 32 32 h32 checkBlocks_63744_63807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63808_63871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63808_63871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63808_63871 :
    ∀ i : Fin 64, indexedBlockCheck (63808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63808 0 32 h0 checkBlocks_63808_63871_part0
  have h64 := extendCertifiedSegment 63808 32 32 h32 checkBlocks_63808_63871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63872_63935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63872_63935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63872_63935 :
    ∀ i : Fin 64, indexedBlockCheck (63872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63872 0 32 h0 checkBlocks_63872_63935_part0
  have h64 := extendCertifiedSegment 63872 32 32 h32 checkBlocks_63872_63935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63936_63999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (63936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63936_63999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (63968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_63936_63999 :
    ∀ i : Fin 64, indexedBlockCheck (63936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 63936 0 32 h0 checkBlocks_63936_63999_part0
  have h64 := extendCertifiedSegment 63936 32 32 h32 checkBlocks_63936_63999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_63488_63999 :
    ∀ i : Fin 512, indexedBlockCheck (63488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (63488 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 63488 0 64 h0 checkBlocks_63488_63551
  have h128 := extendCertifiedSegment 63488 64 64 h64 checkBlocks_63552_63615
  have h192 := extendCertifiedSegment 63488 128 64 h128 checkBlocks_63616_63679
  have h256 := extendCertifiedSegment 63488 192 64 h192 checkBlocks_63680_63743
  have h320 := extendCertifiedSegment 63488 256 64 h256 checkBlocks_63744_63807
  have h384 := extendCertifiedSegment 63488 320 64 h320 checkBlocks_63808_63871
  have h448 := extendCertifiedSegment 63488 384 64 h384 checkBlocks_63872_63935
  have h512 := extendCertifiedSegment 63488 448 64 h448 checkBlocks_63936_63999
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_64000_64063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64000_64063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64000_64063 :
    ∀ i : Fin 64, indexedBlockCheck (64000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64000 0 32 h0 checkBlocks_64000_64063_part0
  have h64 := extendCertifiedSegment 64000 32 32 h32 checkBlocks_64000_64063_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64064_64127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64064_64127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64064_64127 :
    ∀ i : Fin 64, indexedBlockCheck (64064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64064 0 32 h0 checkBlocks_64064_64127_part0
  have h64 := extendCertifiedSegment 64064 32 32 h32 checkBlocks_64064_64127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64128_64191_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64128_64191_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64128_64191 :
    ∀ i : Fin 64, indexedBlockCheck (64128 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64128 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64128 0 32 h0 checkBlocks_64128_64191_part0
  have h64 := extendCertifiedSegment 64128 32 32 h32 checkBlocks_64128_64191_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64192_64255_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64192_64255_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64192_64255 :
    ∀ i : Fin 64, indexedBlockCheck (64192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64192 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64192 0 32 h0 checkBlocks_64192_64255_part0
  have h64 := extendCertifiedSegment 64192 32 32 h32 checkBlocks_64192_64255_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64256_64319_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64256_64319_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64256_64319 :
    ∀ i : Fin 64, indexedBlockCheck (64256 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64256 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64256 0 32 h0 checkBlocks_64256_64319_part0
  have h64 := extendCertifiedSegment 64256 32 32 h32 checkBlocks_64256_64319_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64320_64383_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64320_64383_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64320_64383 :
    ∀ i : Fin 64, indexedBlockCheck (64320 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64320 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64320 0 32 h0 checkBlocks_64320_64383_part0
  have h64 := extendCertifiedSegment 64320 32 32 h32 checkBlocks_64320_64383_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64384_64447_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64384_64447_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64384_64447 :
    ∀ i : Fin 64, indexedBlockCheck (64384 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64384 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64384 0 32 h0 checkBlocks_64384_64447_part0
  have h64 := extendCertifiedSegment 64384 32 32 h32 checkBlocks_64384_64447_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64448_64511_part0 :
    ∀ i : Fin 32, indexedBlockCheck (64448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64448_64511_part1 :
    ∀ i : Fin 32, indexedBlockCheck (64480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64448_64511 :
    ∀ i : Fin 64, indexedBlockCheck (64448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64448 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 64448 0 32 h0 checkBlocks_64448_64511_part0
  have h64 := extendCertifiedSegment 64448 32 32 h32 checkBlocks_64448_64511_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_64000_64511 :
    ∀ i : Fin 512, indexedBlockCheck (64000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (64000 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 64000 0 64 h0 checkBlocks_64000_64063
  have h128 := extendCertifiedSegment 64000 64 64 h64 checkBlocks_64064_64127
  have h192 := extendCertifiedSegment 64000 128 64 h128 checkBlocks_64128_64191
  have h256 := extendCertifiedSegment 64000 192 64 h192 checkBlocks_64192_64255
  have h320 := extendCertifiedSegment 64000 256 64 h256 checkBlocks_64256_64319
  have h384 := extendCertifiedSegment 64000 320 64 h320 checkBlocks_64320_64383
  have h448 := extendCertifiedSegment 64000 384 64 h384 checkBlocks_64384_64447
  have h512 := extendCertifiedSegment 64000 448 64 h448 checkBlocks_64448_64511
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [62464, 64512) passes the packed checker. -/
public theorem blocks_in_62464_64512 :
    ∀ i : Fin 2048, indexedBlockCheck (62464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (62464 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 62464 0 512 h0 checkBlocks_62464_62975
  have h1024 := extendCertifiedSegment 62464 512 512 h512 checkBlocks_62976_63487
  have h1536 := extendCertifiedSegment 62464 1024 512 h1024 checkBlocks_63488_63999
  have h2048 := extendCertifiedSegment 62464 1536 512 h1536 checkBlocks_64000_64511
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
