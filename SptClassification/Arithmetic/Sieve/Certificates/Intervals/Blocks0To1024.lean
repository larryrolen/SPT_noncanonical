/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 0 through 1023 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_0_63 :
    ∀ i : Fin 64, indexedBlockCheck (0 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_64_127 :
    ∀ i : Fin 64, indexedBlockCheck (64 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_128_191 :
    ∀ i : Fin 64, indexedBlockCheck (128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_192_255 :
    ∀ i : Fin 64, indexedBlockCheck (192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_256_319 :
    ∀ i : Fin 64, indexedBlockCheck (256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_320_383 :
    ∀ i : Fin 64, indexedBlockCheck (320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_384_447 :
    ∀ i : Fin 64, indexedBlockCheck (384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_448_511 :
    ∀ i : Fin 64, indexedBlockCheck (448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_0_511 :
    ∀ i : Fin 512, indexedBlockCheck (0 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (0 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 0 0 64 h0 checkBlocks_0_63
  have h128 := extendCertifiedSegment 0 64 64 h64 checkBlocks_64_127
  have h192 := extendCertifiedSegment 0 128 64 h128 checkBlocks_128_191
  have h256 := extendCertifiedSegment 0 192 64 h192 checkBlocks_192_255
  have h320 := extendCertifiedSegment 0 256 64 h256 checkBlocks_256_319
  have h384 := extendCertifiedSegment 0 320 64 h320 checkBlocks_320_383
  have h448 := extendCertifiedSegment 0 384 64 h384 checkBlocks_384_447
  have h512 := extendCertifiedSegment 0 448 64 h448 checkBlocks_448_511
  intro i
  exact h512 i.val i.isLt
private theorem checkBlocks_512_575 :
    ∀ i : Fin 64, indexedBlockCheck (512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_576_639 :
    ∀ i : Fin 64, indexedBlockCheck (576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_640_703 :
    ∀ i : Fin 64, indexedBlockCheck (640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_704_767 :
    ∀ i : Fin 64, indexedBlockCheck (704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_768_831 :
    ∀ i : Fin 64, indexedBlockCheck (768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_832_895 :
    ∀ i : Fin 64, indexedBlockCheck (832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_896_959 :
    ∀ i : Fin 64, indexedBlockCheck (896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_960_1023 :
    ∀ i : Fin 64, indexedBlockCheck (960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_512_1023 :
    ∀ i : Fin 512, indexedBlockCheck (512 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (512 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 512 0 64 h0 checkBlocks_512_575
  have h128 := extendCertifiedSegment 512 64 64 h64 checkBlocks_576_639
  have h192 := extendCertifiedSegment 512 128 64 h128 checkBlocks_640_703
  have h256 := extendCertifiedSegment 512 192 64 h192 checkBlocks_704_767
  have h320 := extendCertifiedSegment 512 256 64 h256 checkBlocks_768_831
  have h384 := extendCertifiedSegment 512 320 64 h320 checkBlocks_832_895
  have h448 := extendCertifiedSegment 512 384 64 h384 checkBlocks_896_959
  have h512 := extendCertifiedSegment 512 448 64 h448 checkBlocks_960_1023
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [0, 1024) passes the packed checker. -/
public theorem blocks_in_0_1024 :
    ∀ i : Fin 1024, indexedBlockCheck (0 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (0 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 0 0 512 h0 checkBlocks_0_511
  have h1024 := extendCertifiedSegment 0 512 512 h512 checkBlocks_512_1023
  intro i
  exact h1024 i.val i.isLt

end SptClassification.Sieve
