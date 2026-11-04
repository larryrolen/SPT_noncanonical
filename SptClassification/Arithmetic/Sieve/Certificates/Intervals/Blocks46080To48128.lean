/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 46080 through 48127 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_46080_46143_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46080_46143_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46080_46143 :
    ∀ i : Fin 64, indexedBlockCheck (46080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46080 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46080 0 32 h0 checkBlocks_46080_46143_part0
  have h64 := extendCertifiedSegment 46080 32 32 h32 checkBlocks_46080_46143_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46144_46207_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46144_46207_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46144_46207 :
    ∀ i : Fin 64, indexedBlockCheck (46144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46144 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46144 0 32 h0 checkBlocks_46144_46207_part0
  have h64 := extendCertifiedSegment 46144 32 32 h32 checkBlocks_46144_46207_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46208_46271_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46208_46271_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46208_46271 :
    ∀ i : Fin 64, indexedBlockCheck (46208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46208 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46208 0 32 h0 checkBlocks_46208_46271_part0
  have h64 := extendCertifiedSegment 46208 32 32 h32 checkBlocks_46208_46271_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46272_46335_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46272_46335_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46272_46335 :
    ∀ i : Fin 64, indexedBlockCheck (46272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46272 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46272 0 32 h0 checkBlocks_46272_46335_part0
  have h64 := extendCertifiedSegment 46272 32 32 h32 checkBlocks_46272_46335_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46336_46399_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46336_46399_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46336_46399 :
    ∀ i : Fin 64, indexedBlockCheck (46336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46336 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46336 0 32 h0 checkBlocks_46336_46399_part0
  have h64 := extendCertifiedSegment 46336 32 32 h32 checkBlocks_46336_46399_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46400_46463_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46400_46463_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46400_46463 :
    ∀ i : Fin 64, indexedBlockCheck (46400 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46400 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46400 0 32 h0 checkBlocks_46400_46463_part0
  have h64 := extendCertifiedSegment 46400 32 32 h32 checkBlocks_46400_46463_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46464_46527_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46464_46527_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46464_46527 :
    ∀ i : Fin 64, indexedBlockCheck (46464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46464 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46464 0 32 h0 checkBlocks_46464_46527_part0
  have h64 := extendCertifiedSegment 46464 32 32 h32 checkBlocks_46464_46527_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46528_46591_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46528_46591_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46528_46591 :
    ∀ i : Fin 64, indexedBlockCheck (46528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46528 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46528 0 32 h0 checkBlocks_46528_46591_part0
  have h64 := extendCertifiedSegment 46528 32 32 h32 checkBlocks_46528_46591_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46080_46591 :
    ∀ i : Fin 512, indexedBlockCheck (46080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46080 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 46080 0 64 h0 checkBlocks_46080_46143
  have h128 := extendCertifiedSegment 46080 64 64 h64 checkBlocks_46144_46207
  have h192 := extendCertifiedSegment 46080 128 64 h128 checkBlocks_46208_46271
  have h256 := extendCertifiedSegment 46080 192 64 h192 checkBlocks_46272_46335
  have h320 := extendCertifiedSegment 46080 256 64 h256 checkBlocks_46336_46399
  have h384 := extendCertifiedSegment 46080 320 64 h320 checkBlocks_46400_46463
  have h448 := extendCertifiedSegment 46080 384 64 h384 checkBlocks_46464_46527
  have h512 := extendCertifiedSegment 46080 448 64 h448 checkBlocks_46528_46591
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_46592_46655_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46592_46655_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46592_46655 :
    ∀ i : Fin 64, indexedBlockCheck (46592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46592 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46592 0 32 h0 checkBlocks_46592_46655_part0
  have h64 := extendCertifiedSegment 46592 32 32 h32 checkBlocks_46592_46655_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46656_46719_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46656_46719_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46656_46719 :
    ∀ i : Fin 64, indexedBlockCheck (46656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46656 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46656 0 32 h0 checkBlocks_46656_46719_part0
  have h64 := extendCertifiedSegment 46656 32 32 h32 checkBlocks_46656_46719_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46720_46783_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46720_46783_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46720_46783 :
    ∀ i : Fin 64, indexedBlockCheck (46720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46720 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46720 0 32 h0 checkBlocks_46720_46783_part0
  have h64 := extendCertifiedSegment 46720 32 32 h32 checkBlocks_46720_46783_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46784_46847_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46784_46847_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46784_46847 :
    ∀ i : Fin 64, indexedBlockCheck (46784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46784 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46784 0 32 h0 checkBlocks_46784_46847_part0
  have h64 := extendCertifiedSegment 46784 32 32 h32 checkBlocks_46784_46847_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46848_46911_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46848_46911_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46848_46911 :
    ∀ i : Fin 64, indexedBlockCheck (46848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46848 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46848 0 32 h0 checkBlocks_46848_46911_part0
  have h64 := extendCertifiedSegment 46848 32 32 h32 checkBlocks_46848_46911_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46912_46975_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46912_46975_part1 :
    ∀ i : Fin 32, indexedBlockCheck (46944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46912_46975 :
    ∀ i : Fin 64, indexedBlockCheck (46912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46912 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46912 0 32 h0 checkBlocks_46912_46975_part0
  have h64 := extendCertifiedSegment 46912 32 32 h32 checkBlocks_46912_46975_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46976_47039_part0 :
    ∀ i : Fin 32, indexedBlockCheck (46976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46976_47039_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46976_47039 :
    ∀ i : Fin 64, indexedBlockCheck (46976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46976 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 46976 0 32 h0 checkBlocks_46976_47039_part0
  have h64 := extendCertifiedSegment 46976 32 32 h32 checkBlocks_46976_47039_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47040_47103_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47040_47103_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47040_47103 :
    ∀ i : Fin 64, indexedBlockCheck (47040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47040 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47040 0 32 h0 checkBlocks_47040_47103_part0
  have h64 := extendCertifiedSegment 47040 32 32 h32 checkBlocks_47040_47103_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_46592_47103 :
    ∀ i : Fin 512, indexedBlockCheck (46592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46592 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 46592 0 64 h0 checkBlocks_46592_46655
  have h128 := extendCertifiedSegment 46592 64 64 h64 checkBlocks_46656_46719
  have h192 := extendCertifiedSegment 46592 128 64 h128 checkBlocks_46720_46783
  have h256 := extendCertifiedSegment 46592 192 64 h192 checkBlocks_46784_46847
  have h320 := extendCertifiedSegment 46592 256 64 h256 checkBlocks_46848_46911
  have h384 := extendCertifiedSegment 46592 320 64 h320 checkBlocks_46912_46975
  have h448 := extendCertifiedSegment 46592 384 64 h384 checkBlocks_46976_47039
  have h512 := extendCertifiedSegment 46592 448 64 h448 checkBlocks_47040_47103
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_47104_47167_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47104_47167_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47104_47167 :
    ∀ i : Fin 64, indexedBlockCheck (47104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47104 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47104 0 32 h0 checkBlocks_47104_47167_part0
  have h64 := extendCertifiedSegment 47104 32 32 h32 checkBlocks_47104_47167_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47168_47231_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47168_47231_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47168_47231 :
    ∀ i : Fin 64, indexedBlockCheck (47168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47168 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47168 0 32 h0 checkBlocks_47168_47231_part0
  have h64 := extendCertifiedSegment 47168 32 32 h32 checkBlocks_47168_47231_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47232_47295_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47232_47295_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47232_47295 :
    ∀ i : Fin 64, indexedBlockCheck (47232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47232 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47232 0 32 h0 checkBlocks_47232_47295_part0
  have h64 := extendCertifiedSegment 47232 32 32 h32 checkBlocks_47232_47295_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47296_47359_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47296_47359_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47296_47359 :
    ∀ i : Fin 64, indexedBlockCheck (47296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47296 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47296 0 32 h0 checkBlocks_47296_47359_part0
  have h64 := extendCertifiedSegment 47296 32 32 h32 checkBlocks_47296_47359_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47360_47423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47360_47423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47360_47423 :
    ∀ i : Fin 64, indexedBlockCheck (47360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47360 0 32 h0 checkBlocks_47360_47423_part0
  have h64 := extendCertifiedSegment 47360 32 32 h32 checkBlocks_47360_47423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47424_47487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47424_47487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47424_47487 :
    ∀ i : Fin 64, indexedBlockCheck (47424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47424 0 32 h0 checkBlocks_47424_47487_part0
  have h64 := extendCertifiedSegment 47424 32 32 h32 checkBlocks_47424_47487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47488_47551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47488_47551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47488_47551 :
    ∀ i : Fin 64, indexedBlockCheck (47488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47488 0 32 h0 checkBlocks_47488_47551_part0
  have h64 := extendCertifiedSegment 47488 32 32 h32 checkBlocks_47488_47551_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47552_47615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47552_47615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47552_47615 :
    ∀ i : Fin 64, indexedBlockCheck (47552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47552 0 32 h0 checkBlocks_47552_47615_part0
  have h64 := extendCertifiedSegment 47552 32 32 h32 checkBlocks_47552_47615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47104_47615 :
    ∀ i : Fin 512, indexedBlockCheck (47104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47104 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 47104 0 64 h0 checkBlocks_47104_47167
  have h128 := extendCertifiedSegment 47104 64 64 h64 checkBlocks_47168_47231
  have h192 := extendCertifiedSegment 47104 128 64 h128 checkBlocks_47232_47295
  have h256 := extendCertifiedSegment 47104 192 64 h192 checkBlocks_47296_47359
  have h320 := extendCertifiedSegment 47104 256 64 h256 checkBlocks_47360_47423
  have h384 := extendCertifiedSegment 47104 320 64 h320 checkBlocks_47424_47487
  have h448 := extendCertifiedSegment 47104 384 64 h384 checkBlocks_47488_47551
  have h512 := extendCertifiedSegment 47104 448 64 h448 checkBlocks_47552_47615
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_47616_47679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47616_47679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47616_47679 :
    ∀ i : Fin 64, indexedBlockCheck (47616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47616 0 32 h0 checkBlocks_47616_47679_part0
  have h64 := extendCertifiedSegment 47616 32 32 h32 checkBlocks_47616_47679_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47680_47743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47680_47743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47680_47743 :
    ∀ i : Fin 64, indexedBlockCheck (47680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47680 0 32 h0 checkBlocks_47680_47743_part0
  have h64 := extendCertifiedSegment 47680 32 32 h32 checkBlocks_47680_47743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47744_47807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47744_47807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47744_47807 :
    ∀ i : Fin 64, indexedBlockCheck (47744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47744 0 32 h0 checkBlocks_47744_47807_part0
  have h64 := extendCertifiedSegment 47744 32 32 h32 checkBlocks_47744_47807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47808_47871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47808_47871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47808_47871 :
    ∀ i : Fin 64, indexedBlockCheck (47808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47808 0 32 h0 checkBlocks_47808_47871_part0
  have h64 := extendCertifiedSegment 47808 32 32 h32 checkBlocks_47808_47871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47872_47935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47872_47935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47872_47935 :
    ∀ i : Fin 64, indexedBlockCheck (47872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47872 0 32 h0 checkBlocks_47872_47935_part0
  have h64 := extendCertifiedSegment 47872 32 32 h32 checkBlocks_47872_47935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47936_47999_part0 :
    ∀ i : Fin 32, indexedBlockCheck (47936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47936_47999_part1 :
    ∀ i : Fin 32, indexedBlockCheck (47968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_47936_47999 :
    ∀ i : Fin 64, indexedBlockCheck (47936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47936 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 47936 0 32 h0 checkBlocks_47936_47999_part0
  have h64 := extendCertifiedSegment 47936 32 32 h32 checkBlocks_47936_47999_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48000_48063_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48000_48063_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48000_48063 :
    ∀ i : Fin 64, indexedBlockCheck (48000 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48000 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48000 0 32 h0 checkBlocks_48000_48063_part0
  have h64 := extendCertifiedSegment 48000 32 32 h32 checkBlocks_48000_48063_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_48064_48127_part0 :
    ∀ i : Fin 32, indexedBlockCheck (48064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48064_48127_part1 :
    ∀ i : Fin 32, indexedBlockCheck (48096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_48064_48127 :
    ∀ i : Fin 64, indexedBlockCheck (48064 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (48064 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 48064 0 32 h0 checkBlocks_48064_48127_part0
  have h64 := extendCertifiedSegment 48064 32 32 h32 checkBlocks_48064_48127_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_47616_48127 :
    ∀ i : Fin 512, indexedBlockCheck (47616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (47616 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 47616 0 64 h0 checkBlocks_47616_47679
  have h128 := extendCertifiedSegment 47616 64 64 h64 checkBlocks_47680_47743
  have h192 := extendCertifiedSegment 47616 128 64 h128 checkBlocks_47744_47807
  have h256 := extendCertifiedSegment 47616 192 64 h192 checkBlocks_47808_47871
  have h320 := extendCertifiedSegment 47616 256 64 h256 checkBlocks_47872_47935
  have h384 := extendCertifiedSegment 47616 320 64 h320 checkBlocks_47936_47999
  have h448 := extendCertifiedSegment 47616 384 64 h384 checkBlocks_48000_48063
  have h512 := extendCertifiedSegment 47616 448 64 h448 checkBlocks_48064_48127
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [46080, 48128) passes the packed checker. -/
public theorem blocks_in_46080_48128 :
    ∀ i : Fin 2048, indexedBlockCheck (46080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (46080 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 46080 0 512 h0 checkBlocks_46080_46591
  have h1024 := extendCertifiedSegment 46080 512 512 h512 checkBlocks_46592_47103
  have h1536 := extendCertifiedSegment 46080 1024 512 h1024 checkBlocks_47104_47615
  have h2048 := extendCertifiedSegment 46080 1536 512 h1536 checkBlocks_47616_48127
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
