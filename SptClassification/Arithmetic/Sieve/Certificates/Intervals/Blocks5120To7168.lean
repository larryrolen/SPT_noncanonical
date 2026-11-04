/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks1024To3072

/-! # Certified checker blocks from 5120 through 7167 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_5120_5183 :
    ∀ i : Fin 64, indexedBlockCheck (5120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5184_5247 :
    ∀ i : Fin 64, indexedBlockCheck (5184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5248_5311 :
    ∀ i : Fin 64, indexedBlockCheck (5248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5312_5375 :
    ∀ i : Fin 64, indexedBlockCheck (5312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5376_5439 :
    ∀ i : Fin 64, indexedBlockCheck (5376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5440_5503 :
    ∀ i : Fin 64, indexedBlockCheck (5440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5504_5567 :
    ∀ i : Fin 64, indexedBlockCheck (5504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5568_5631 :
    ∀ i : Fin 64, indexedBlockCheck (5568 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_5632_5695 :
    ∀ i : Fin 64, indexedBlockCheck (5632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5696_5759 :
    ∀ i : Fin 64, indexedBlockCheck (5696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5760_5823 :
    ∀ i : Fin 64, indexedBlockCheck (5760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5824_5887 :
    ∀ i : Fin 64, indexedBlockCheck (5824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5888_5951 :
    ∀ i : Fin 64, indexedBlockCheck (5888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_5952_6015 :
    ∀ i : Fin 64, indexedBlockCheck (5952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6016_6079 :
    ∀ i : Fin 64, indexedBlockCheck (6016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6080_6143 :
    ∀ i : Fin 64, indexedBlockCheck (6080 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_6144_6207 :
    ∀ i : Fin 64, indexedBlockCheck (6144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6208_6271 :
    ∀ i : Fin 64, indexedBlockCheck (6208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6272_6335 :
    ∀ i : Fin 64, indexedBlockCheck (6272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6336_6399 :
    ∀ i : Fin 64, indexedBlockCheck (6336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6400_6463 :
    ∀ i : Fin 64, indexedBlockCheck (6400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6464_6527 :
    ∀ i : Fin 64, indexedBlockCheck (6464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6528_6591 :
    ∀ i : Fin 64, indexedBlockCheck (6528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6592_6655 :
    ∀ i : Fin 64, indexedBlockCheck (6592 + i.val) = true := by
  decide +kernel

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

private theorem checkBlocks_6656_6719 :
    ∀ i : Fin 64, indexedBlockCheck (6656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6720_6783 :
    ∀ i : Fin 64, indexedBlockCheck (6720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6784_6847 :
    ∀ i : Fin 64, indexedBlockCheck (6784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6848_6911 :
    ∀ i : Fin 64, indexedBlockCheck (6848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6912_6975 :
    ∀ i : Fin 64, indexedBlockCheck (6912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_6976_7039 :
    ∀ i : Fin 64, indexedBlockCheck (6976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7040_7103 :
    ∀ i : Fin 64, indexedBlockCheck (7040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_7104_7167 :
    ∀ i : Fin 64, indexedBlockCheck (7104 + i.val) = true := by
  decide +kernel

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
