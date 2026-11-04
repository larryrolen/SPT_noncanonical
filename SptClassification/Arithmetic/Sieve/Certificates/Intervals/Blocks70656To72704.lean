/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 70656 through 72703 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_70656_70719 :
    ∀ i : Fin 64, indexedBlockCheck (70656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70720_70783 :
    ∀ i : Fin 64, indexedBlockCheck (70720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70784_70847 :
    ∀ i : Fin 64, indexedBlockCheck (70784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70848_70911 :
    ∀ i : Fin 64, indexedBlockCheck (70848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70912_70975 :
    ∀ i : Fin 64, indexedBlockCheck (70912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70976_71039 :
    ∀ i : Fin 64, indexedBlockCheck (70976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71040_71103 :
    ∀ i : Fin 64, indexedBlockCheck (71040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71104_71167 :
    ∀ i : Fin 64, indexedBlockCheck (71104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70656_71167 :
    ∀ i : Fin 512, indexedBlockCheck (70656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70656 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 70656 0 64 h0 checkBlocks_70656_70719
  have h128 := extendCertifiedSegment 70656 64 64 h64 checkBlocks_70720_70783
  have h192 := extendCertifiedSegment 70656 128 64 h128 checkBlocks_70784_70847
  have h256 := extendCertifiedSegment 70656 192 64 h192 checkBlocks_70848_70911
  have h320 := extendCertifiedSegment 70656 256 64 h256 checkBlocks_70912_70975
  have h384 := extendCertifiedSegment 70656 320 64 h320 checkBlocks_70976_71039
  have h448 := extendCertifiedSegment 70656 384 64 h384 checkBlocks_71040_71103
  have h512 := extendCertifiedSegment 70656 448 64 h448 checkBlocks_71104_71167
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_71168_71231 :
    ∀ i : Fin 64, indexedBlockCheck (71168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71232_71295 :
    ∀ i : Fin 64, indexedBlockCheck (71232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71296_71359 :
    ∀ i : Fin 64, indexedBlockCheck (71296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71360_71423 :
    ∀ i : Fin 64, indexedBlockCheck (71360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71424_71487 :
    ∀ i : Fin 64, indexedBlockCheck (71424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71488_71551 :
    ∀ i : Fin 64, indexedBlockCheck (71488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71552_71615 :
    ∀ i : Fin 64, indexedBlockCheck (71552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71616_71679 :
    ∀ i : Fin 64, indexedBlockCheck (71616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71168_71679 :
    ∀ i : Fin 512, indexedBlockCheck (71168 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71168 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 71168 0 64 h0 checkBlocks_71168_71231
  have h128 := extendCertifiedSegment 71168 64 64 h64 checkBlocks_71232_71295
  have h192 := extendCertifiedSegment 71168 128 64 h128 checkBlocks_71296_71359
  have h256 := extendCertifiedSegment 71168 192 64 h192 checkBlocks_71360_71423
  have h320 := extendCertifiedSegment 71168 256 64 h256 checkBlocks_71424_71487
  have h384 := extendCertifiedSegment 71168 320 64 h320 checkBlocks_71488_71551
  have h448 := extendCertifiedSegment 71168 384 64 h384 checkBlocks_71552_71615
  have h512 := extendCertifiedSegment 71168 448 64 h448 checkBlocks_71616_71679
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_71680_71743 :
    ∀ i : Fin 64, indexedBlockCheck (71680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71744_71807 :
    ∀ i : Fin 64, indexedBlockCheck (71744 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71808_71871 :
    ∀ i : Fin 64, indexedBlockCheck (71808 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71872_71935 :
    ∀ i : Fin 64, indexedBlockCheck (71872 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71936_71999 :
    ∀ i : Fin 64, indexedBlockCheck (71936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72000_72063 :
    ∀ i : Fin 64, indexedBlockCheck (72000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72064_72127 :
    ∀ i : Fin 64, indexedBlockCheck (72064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72128_72191 :
    ∀ i : Fin 64, indexedBlockCheck (72128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_71680_72191 :
    ∀ i : Fin 512, indexedBlockCheck (71680 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (71680 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 71680 0 64 h0 checkBlocks_71680_71743
  have h128 := extendCertifiedSegment 71680 64 64 h64 checkBlocks_71744_71807
  have h192 := extendCertifiedSegment 71680 128 64 h128 checkBlocks_71808_71871
  have h256 := extendCertifiedSegment 71680 192 64 h192 checkBlocks_71872_71935
  have h320 := extendCertifiedSegment 71680 256 64 h256 checkBlocks_71936_71999
  have h384 := extendCertifiedSegment 71680 320 64 h320 checkBlocks_72000_72063
  have h448 := extendCertifiedSegment 71680 384 64 h384 checkBlocks_72064_72127
  have h512 := extendCertifiedSegment 71680 448 64 h448 checkBlocks_72128_72191
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_72192_72255 :
    ∀ i : Fin 64, indexedBlockCheck (72192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72256_72319 :
    ∀ i : Fin 64, indexedBlockCheck (72256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72320_72383 :
    ∀ i : Fin 64, indexedBlockCheck (72320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72384_72447 :
    ∀ i : Fin 64, indexedBlockCheck (72384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72448_72511 :
    ∀ i : Fin 64, indexedBlockCheck (72448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72512_72575 :
    ∀ i : Fin 64, indexedBlockCheck (72512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72576_72639 :
    ∀ i : Fin 64, indexedBlockCheck (72576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72640_72703 :
    ∀ i : Fin 64, indexedBlockCheck (72640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_72192_72703 :
    ∀ i : Fin 512, indexedBlockCheck (72192 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (72192 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 72192 0 64 h0 checkBlocks_72192_72255
  have h128 := extendCertifiedSegment 72192 64 64 h64 checkBlocks_72256_72319
  have h192 := extendCertifiedSegment 72192 128 64 h128 checkBlocks_72320_72383
  have h256 := extendCertifiedSegment 72192 192 64 h192 checkBlocks_72384_72447
  have h320 := extendCertifiedSegment 72192 256 64 h256 checkBlocks_72448_72511
  have h384 := extendCertifiedSegment 72192 320 64 h320 checkBlocks_72512_72575
  have h448 := extendCertifiedSegment 72192 384 64 h384 checkBlocks_72576_72639
  have h512 := extendCertifiedSegment 72192 448 64 h448 checkBlocks_72640_72703
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [70656, 72704) passes the packed checker. -/
public theorem blocks_in_70656_72704 :
    ∀ i : Fin 2048, indexedBlockCheck (70656 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70656 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 70656 0 512 h0 checkBlocks_70656_71167
  have h1024 := extendCertifiedSegment 70656 512 512 h512 checkBlocks_71168_71679
  have h1536 := extendCertifiedSegment 70656 1024 512 h1024 checkBlocks_71680_72191
  have h2048 := extendCertifiedSegment 70656 1536 512 h1536 checkBlocks_72192_72703
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
