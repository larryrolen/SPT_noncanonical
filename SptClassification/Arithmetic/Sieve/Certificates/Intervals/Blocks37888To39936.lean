/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 37888 through 39935 -/

public section

namespace SptClassification.Sieve

-- Bound memory by checking small certificate pieces sequentially.
set_option Elab.async false

private theorem checkBlocks_37888_37951_part0 :
    ∀ i : Fin 32, indexedBlockCheck (37888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37888_37951_part1 :
    ∀ i : Fin 32, indexedBlockCheck (37920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37888_37951 :
    ∀ i : Fin 64, indexedBlockCheck (37888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (37888 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 37888 0 32 h0 checkBlocks_37888_37951_part0
  have h64 := extendCertifiedSegment 37888 32 32 h32 checkBlocks_37888_37951_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_37952_38015_part0 :
    ∀ i : Fin 32, indexedBlockCheck (37952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37952_38015_part1 :
    ∀ i : Fin 32, indexedBlockCheck (37984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37952_38015 :
    ∀ i : Fin 64, indexedBlockCheck (37952 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (37952 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 37952 0 32 h0 checkBlocks_37952_38015_part0
  have h64 := extendCertifiedSegment 37952 32 32 h32 checkBlocks_37952_38015_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38016_38079_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38016_38079_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38016_38079 :
    ∀ i : Fin 64, indexedBlockCheck (38016 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38016 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38016 0 32 h0 checkBlocks_38016_38079_part0
  have h64 := extendCertifiedSegment 38016 32 32 h32 checkBlocks_38016_38079_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38080_38143_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38080_38143_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38080_38143 :
    ∀ i : Fin 64, indexedBlockCheck (38080 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38080 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38080 0 32 h0 checkBlocks_38080_38143_part0
  have h64 := extendCertifiedSegment 38080 32 32 h32 checkBlocks_38080_38143_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38144_38207_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38144_38207_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38144_38207 :
    ∀ i : Fin 64, indexedBlockCheck (38144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38144 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38144 0 32 h0 checkBlocks_38144_38207_part0
  have h64 := extendCertifiedSegment 38144 32 32 h32 checkBlocks_38144_38207_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38208_38271_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38208_38271_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38208_38271 :
    ∀ i : Fin 64, indexedBlockCheck (38208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38208 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38208 0 32 h0 checkBlocks_38208_38271_part0
  have h64 := extendCertifiedSegment 38208 32 32 h32 checkBlocks_38208_38271_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38272_38335_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38272_38335_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38272_38335 :
    ∀ i : Fin 64, indexedBlockCheck (38272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38272 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38272 0 32 h0 checkBlocks_38272_38335_part0
  have h64 := extendCertifiedSegment 38272 32 32 h32 checkBlocks_38272_38335_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38336_38399_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38336_38399_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38336_38399 :
    ∀ i : Fin 64, indexedBlockCheck (38336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38336 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38336 0 32 h0 checkBlocks_38336_38399_part0
  have h64 := extendCertifiedSegment 38336 32 32 h32 checkBlocks_38336_38399_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_37888_38399 :
    ∀ i : Fin 512, indexedBlockCheck (37888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (37888 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 37888 0 64 h0 checkBlocks_37888_37951
  have h128 := extendCertifiedSegment 37888 64 64 h64 checkBlocks_37952_38015
  have h192 := extendCertifiedSegment 37888 128 64 h128 checkBlocks_38016_38079
  have h256 := extendCertifiedSegment 37888 192 64 h192 checkBlocks_38080_38143
  have h320 := extendCertifiedSegment 37888 256 64 h256 checkBlocks_38144_38207
  have h384 := extendCertifiedSegment 37888 320 64 h320 checkBlocks_38208_38271
  have h448 := extendCertifiedSegment 37888 384 64 h384 checkBlocks_38272_38335
  have h512 := extendCertifiedSegment 37888 448 64 h448 checkBlocks_38336_38399
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_38400_38463_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38400_38463_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38400_38463 :
    ∀ i : Fin 64, indexedBlockCheck (38400 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38400 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38400 0 32 h0 checkBlocks_38400_38463_part0
  have h64 := extendCertifiedSegment 38400 32 32 h32 checkBlocks_38400_38463_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38464_38527_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38464_38527_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38464_38527 :
    ∀ i : Fin 64, indexedBlockCheck (38464 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38464 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38464 0 32 h0 checkBlocks_38464_38527_part0
  have h64 := extendCertifiedSegment 38464 32 32 h32 checkBlocks_38464_38527_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38528_38591_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38528_38591_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38528_38591 :
    ∀ i : Fin 64, indexedBlockCheck (38528 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38528 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38528 0 32 h0 checkBlocks_38528_38591_part0
  have h64 := extendCertifiedSegment 38528 32 32 h32 checkBlocks_38528_38591_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38592_38655_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38592_38655_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38592_38655 :
    ∀ i : Fin 64, indexedBlockCheck (38592 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38592 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38592 0 32 h0 checkBlocks_38592_38655_part0
  have h64 := extendCertifiedSegment 38592 32 32 h32 checkBlocks_38592_38655_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38656_38719_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38656_38719_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38656_38719 :
    ∀ i : Fin 64, indexedBlockCheck (38656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38656 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38656 0 32 h0 checkBlocks_38656_38719_part0
  have h64 := extendCertifiedSegment 38656 32 32 h32 checkBlocks_38656_38719_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38720_38783_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38720_38783_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38720_38783 :
    ∀ i : Fin 64, indexedBlockCheck (38720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38720 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38720 0 32 h0 checkBlocks_38720_38783_part0
  have h64 := extendCertifiedSegment 38720 32 32 h32 checkBlocks_38720_38783_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38784_38847_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38784_38847_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38784_38847 :
    ∀ i : Fin 64, indexedBlockCheck (38784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38784 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38784 0 32 h0 checkBlocks_38784_38847_part0
  have h64 := extendCertifiedSegment 38784 32 32 h32 checkBlocks_38784_38847_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38848_38911_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38848_38911_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38848_38911 :
    ∀ i : Fin 64, indexedBlockCheck (38848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38848 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38848 0 32 h0 checkBlocks_38848_38911_part0
  have h64 := extendCertifiedSegment 38848 32 32 h32 checkBlocks_38848_38911_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38400_38911 :
    ∀ i : Fin 512, indexedBlockCheck (38400 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38400 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 38400 0 64 h0 checkBlocks_38400_38463
  have h128 := extendCertifiedSegment 38400 64 64 h64 checkBlocks_38464_38527
  have h192 := extendCertifiedSegment 38400 128 64 h128 checkBlocks_38528_38591
  have h256 := extendCertifiedSegment 38400 192 64 h192 checkBlocks_38592_38655
  have h320 := extendCertifiedSegment 38400 256 64 h256 checkBlocks_38656_38719
  have h384 := extendCertifiedSegment 38400 320 64 h320 checkBlocks_38720_38783
  have h448 := extendCertifiedSegment 38400 384 64 h384 checkBlocks_38784_38847
  have h512 := extendCertifiedSegment 38400 448 64 h448 checkBlocks_38848_38911
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_38912_38975_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38912_38975_part1 :
    ∀ i : Fin 32, indexedBlockCheck (38944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38912_38975 :
    ∀ i : Fin 64, indexedBlockCheck (38912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38912 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38912 0 32 h0 checkBlocks_38912_38975_part0
  have h64 := extendCertifiedSegment 38912 32 32 h32 checkBlocks_38912_38975_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38976_39039_part0 :
    ∀ i : Fin 32, indexedBlockCheck (38976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38976_39039_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_38976_39039 :
    ∀ i : Fin 64, indexedBlockCheck (38976 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38976 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 38976 0 32 h0 checkBlocks_38976_39039_part0
  have h64 := extendCertifiedSegment 38976 32 32 h32 checkBlocks_38976_39039_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39040_39103_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39040_39103_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39040_39103 :
    ∀ i : Fin 64, indexedBlockCheck (39040 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39040 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39040 0 32 h0 checkBlocks_39040_39103_part0
  have h64 := extendCertifiedSegment 39040 32 32 h32 checkBlocks_39040_39103_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39104_39167_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39104_39167_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39104_39167 :
    ∀ i : Fin 64, indexedBlockCheck (39104 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39104 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39104 0 32 h0 checkBlocks_39104_39167_part0
  have h64 := extendCertifiedSegment 39104 32 32 h32 checkBlocks_39104_39167_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39168_39231_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39168_39231_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39168_39231 :
    ∀ i : Fin 64, indexedBlockCheck (39168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39168 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39168 0 32 h0 checkBlocks_39168_39231_part0
  have h64 := extendCertifiedSegment 39168 32 32 h32 checkBlocks_39168_39231_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39232_39295_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39232_39295_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39232_39295 :
    ∀ i : Fin 64, indexedBlockCheck (39232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39232 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39232 0 32 h0 checkBlocks_39232_39295_part0
  have h64 := extendCertifiedSegment 39232 32 32 h32 checkBlocks_39232_39295_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39296_39359_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39296_39359_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39296_39359 :
    ∀ i : Fin 64, indexedBlockCheck (39296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39296 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39296 0 32 h0 checkBlocks_39296_39359_part0
  have h64 := extendCertifiedSegment 39296 32 32 h32 checkBlocks_39296_39359_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39360_39423_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39360_39423_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39360_39423 :
    ∀ i : Fin 64, indexedBlockCheck (39360 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39360 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39360 0 32 h0 checkBlocks_39360_39423_part0
  have h64 := extendCertifiedSegment 39360 32 32 h32 checkBlocks_39360_39423_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_38912_39423 :
    ∀ i : Fin 512, indexedBlockCheck (38912 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (38912 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 38912 0 64 h0 checkBlocks_38912_38975
  have h128 := extendCertifiedSegment 38912 64 64 h64 checkBlocks_38976_39039
  have h192 := extendCertifiedSegment 38912 128 64 h128 checkBlocks_39040_39103
  have h256 := extendCertifiedSegment 38912 192 64 h192 checkBlocks_39104_39167
  have h320 := extendCertifiedSegment 38912 256 64 h256 checkBlocks_39168_39231
  have h384 := extendCertifiedSegment 38912 320 64 h320 checkBlocks_39232_39295
  have h448 := extendCertifiedSegment 38912 384 64 h384 checkBlocks_39296_39359
  have h512 := extendCertifiedSegment 38912 448 64 h448 checkBlocks_39360_39423
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_39424_39487_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39424_39487_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39424_39487 :
    ∀ i : Fin 64, indexedBlockCheck (39424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39424 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39424 0 32 h0 checkBlocks_39424_39487_part0
  have h64 := extendCertifiedSegment 39424 32 32 h32 checkBlocks_39424_39487_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39488_39551_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39488_39551_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39488_39551 :
    ∀ i : Fin 64, indexedBlockCheck (39488 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39488 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39488 0 32 h0 checkBlocks_39488_39551_part0
  have h64 := extendCertifiedSegment 39488 32 32 h32 checkBlocks_39488_39551_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39552_39615_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39552_39615_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39552_39615 :
    ∀ i : Fin 64, indexedBlockCheck (39552 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39552 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39552 0 32 h0 checkBlocks_39552_39615_part0
  have h64 := extendCertifiedSegment 39552 32 32 h32 checkBlocks_39552_39615_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39616_39679_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39616_39679_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39616_39679 :
    ∀ i : Fin 64, indexedBlockCheck (39616 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39616 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39616 0 32 h0 checkBlocks_39616_39679_part0
  have h64 := extendCertifiedSegment 39616 32 32 h32 checkBlocks_39616_39679_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39680_39743_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39680_39743_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39680_39743 :
    ∀ i : Fin 64, indexedBlockCheck (39680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39680 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39680 0 32 h0 checkBlocks_39680_39743_part0
  have h64 := extendCertifiedSegment 39680 32 32 h32 checkBlocks_39680_39743_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39744_39807_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39744_39807_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39744_39807 :
    ∀ i : Fin 64, indexedBlockCheck (39744 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39744 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39744 0 32 h0 checkBlocks_39744_39807_part0
  have h64 := extendCertifiedSegment 39744 32 32 h32 checkBlocks_39744_39807_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39808_39871_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39808_39871_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39808_39871 :
    ∀ i : Fin 64, indexedBlockCheck (39808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39808 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39808 0 32 h0 checkBlocks_39808_39871_part0
  have h64 := extendCertifiedSegment 39808 32 32 h32 checkBlocks_39808_39871_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39872_39935_part0 :
    ∀ i : Fin 32, indexedBlockCheck (39872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39872_39935_part1 :
    ∀ i : Fin 32, indexedBlockCheck (39904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39872_39935 :
    ∀ i : Fin 64, indexedBlockCheck (39872 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39872 + i) = true := by
    intro i hi
    omega
  have h32 := extendCertifiedSegment 39872 0 32 h0 checkBlocks_39872_39935_part0
  have h64 := extendCertifiedSegment 39872 32 32 h32 checkBlocks_39872_39935_part1
  intro i
  exact h64 i.val i.isLt

private theorem checkBlocks_39424_39935 :
    ∀ i : Fin 512, indexedBlockCheck (39424 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39424 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 39424 0 64 h0 checkBlocks_39424_39487
  have h128 := extendCertifiedSegment 39424 64 64 h64 checkBlocks_39488_39551
  have h192 := extendCertifiedSegment 39424 128 64 h128 checkBlocks_39552_39615
  have h256 := extendCertifiedSegment 39424 192 64 h192 checkBlocks_39616_39679
  have h320 := extendCertifiedSegment 39424 256 64 h256 checkBlocks_39680_39743
  have h384 := extendCertifiedSegment 39424 320 64 h320 checkBlocks_39744_39807
  have h448 := extendCertifiedSegment 39424 384 64 h384 checkBlocks_39808_39871
  have h512 := extendCertifiedSegment 39424 448 64 h448 checkBlocks_39872_39935
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [37888, 39936) passes the packed checker. -/
public theorem blocks_in_37888_39936 :
    ∀ i : Fin 2048, indexedBlockCheck (37888 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (37888 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 37888 0 512 h0 checkBlocks_37888_38399
  have h1024 := extendCertifiedSegment 37888 512 512 h512 checkBlocks_38400_38911
  have h1536 := extendCertifiedSegment 37888 1024 512 h1024 checkBlocks_38912_39423
  have h2048 := extendCertifiedSegment 37888 1536 512 h1536 checkBlocks_39424_39935
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
