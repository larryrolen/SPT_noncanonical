/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 54272 through 56319 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_54272_54335 :
    ∀ i : Fin 64, indexedBlockCheck (54272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54336_54399 :
    ∀ i : Fin 64, indexedBlockCheck (54336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54400_54463 :
    ∀ i : Fin 64, indexedBlockCheck (54400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54464_54527 :
    ∀ i : Fin 64, indexedBlockCheck (54464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54528_54591 :
    ∀ i : Fin 64, indexedBlockCheck (54528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54592_54655 :
    ∀ i : Fin 64, indexedBlockCheck (54592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54656_54719 :
    ∀ i : Fin 64, indexedBlockCheck (54656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54720_54783 :
    ∀ i : Fin 64, indexedBlockCheck (54720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54272_54783 :
    ∀ i : Fin 512, indexedBlockCheck (54272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (54272 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 54272 0 64 h0 checkBlocks_54272_54335
  have h128 := extendCertifiedSegment 54272 64 64 h64 checkBlocks_54336_54399
  have h192 := extendCertifiedSegment 54272 128 64 h128 checkBlocks_54400_54463
  have h256 := extendCertifiedSegment 54272 192 64 h192 checkBlocks_54464_54527
  have h320 := extendCertifiedSegment 54272 256 64 h256 checkBlocks_54528_54591
  have h384 := extendCertifiedSegment 54272 320 64 h320 checkBlocks_54592_54655
  have h448 := extendCertifiedSegment 54272 384 64 h384 checkBlocks_54656_54719
  have h512 := extendCertifiedSegment 54272 448 64 h448 checkBlocks_54720_54783
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_54784_54847 :
    ∀ i : Fin 64, indexedBlockCheck (54784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54848_54911 :
    ∀ i : Fin 64, indexedBlockCheck (54848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54912_54975 :
    ∀ i : Fin 64, indexedBlockCheck (54912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54976_55039 :
    ∀ i : Fin 64, indexedBlockCheck (54976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55040_55103 :
    ∀ i : Fin 64, indexedBlockCheck (55040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55104_55167 :
    ∀ i : Fin 64, indexedBlockCheck (55104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55168_55231 :
    ∀ i : Fin 64, indexedBlockCheck (55168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55232_55295 :
    ∀ i : Fin 64, indexedBlockCheck (55232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54784_55295 :
    ∀ i : Fin 512, indexedBlockCheck (54784 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (54784 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 54784 0 64 h0 checkBlocks_54784_54847
  have h128 := extendCertifiedSegment 54784 64 64 h64 checkBlocks_54848_54911
  have h192 := extendCertifiedSegment 54784 128 64 h128 checkBlocks_54912_54975
  have h256 := extendCertifiedSegment 54784 192 64 h192 checkBlocks_54976_55039
  have h320 := extendCertifiedSegment 54784 256 64 h256 checkBlocks_55040_55103
  have h384 := extendCertifiedSegment 54784 320 64 h320 checkBlocks_55104_55167
  have h448 := extendCertifiedSegment 54784 384 64 h384 checkBlocks_55168_55231
  have h512 := extendCertifiedSegment 54784 448 64 h448 checkBlocks_55232_55295
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_55296_55359 :
    ∀ i : Fin 64, indexedBlockCheck (55296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55360_55423 :
    ∀ i : Fin 64, indexedBlockCheck (55360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55424_55487 :
    ∀ i : Fin 64, indexedBlockCheck (55424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55488_55551 :
    ∀ i : Fin 64, indexedBlockCheck (55488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55552_55615 :
    ∀ i : Fin 64, indexedBlockCheck (55552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55616_55679 :
    ∀ i : Fin 64, indexedBlockCheck (55616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55680_55743 :
    ∀ i : Fin 64, indexedBlockCheck (55680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55744_55807 :
    ∀ i : Fin 64, indexedBlockCheck (55744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55296_55807 :
    ∀ i : Fin 512, indexedBlockCheck (55296 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (55296 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 55296 0 64 h0 checkBlocks_55296_55359
  have h128 := extendCertifiedSegment 55296 64 64 h64 checkBlocks_55360_55423
  have h192 := extendCertifiedSegment 55296 128 64 h128 checkBlocks_55424_55487
  have h256 := extendCertifiedSegment 55296 192 64 h192 checkBlocks_55488_55551
  have h320 := extendCertifiedSegment 55296 256 64 h256 checkBlocks_55552_55615
  have h384 := extendCertifiedSegment 55296 320 64 h320 checkBlocks_55616_55679
  have h448 := extendCertifiedSegment 55296 384 64 h384 checkBlocks_55680_55743
  have h512 := extendCertifiedSegment 55296 448 64 h448 checkBlocks_55744_55807
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_55808_55871 :
    ∀ i : Fin 64, indexedBlockCheck (55808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55872_55935 :
    ∀ i : Fin 64, indexedBlockCheck (55872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55936_55999 :
    ∀ i : Fin 64, indexedBlockCheck (55936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56000_56063 :
    ∀ i : Fin 64, indexedBlockCheck (56000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56064_56127 :
    ∀ i : Fin 64, indexedBlockCheck (56064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56128_56191 :
    ∀ i : Fin 64, indexedBlockCheck (56128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56192_56255 :
    ∀ i : Fin 64, indexedBlockCheck (56192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_56256_56319 :
    ∀ i : Fin 64, indexedBlockCheck (56256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_55808_56319 :
    ∀ i : Fin 512, indexedBlockCheck (55808 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (55808 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 55808 0 64 h0 checkBlocks_55808_55871
  have h128 := extendCertifiedSegment 55808 64 64 h64 checkBlocks_55872_55935
  have h192 := extendCertifiedSegment 55808 128 64 h128 checkBlocks_55936_55999
  have h256 := extendCertifiedSegment 55808 192 64 h192 checkBlocks_56000_56063
  have h320 := extendCertifiedSegment 55808 256 64 h256 checkBlocks_56064_56127
  have h384 := extendCertifiedSegment 55808 320 64 h320 checkBlocks_56128_56191
  have h448 := extendCertifiedSegment 55808 384 64 h384 checkBlocks_56192_56255
  have h512 := extendCertifiedSegment 55808 448 64 h448 checkBlocks_56256_56319
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [54272, 56320) passes the packed checker. -/
public theorem blocks_in_54272_56320 :
    ∀ i : Fin 2048, indexedBlockCheck (54272 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (54272 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 54272 0 512 h0 checkBlocks_54272_54783
  have h1024 := extendCertifiedSegment 54272 512 512 h512 checkBlocks_54784_55295
  have h1536 := extendCertifiedSegment 54272 1024 512 h1024 checkBlocks_55296_55807
  have h2048 := extendCertifiedSegment 54272 1536 512 h1536 checkBlocks_55808_56319
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
