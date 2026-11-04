/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks89088To91136

/-! # Certified checker blocks from 93184 through 95231 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_93184_93247 :
    ∀ i : Fin 64, indexedBlockCheck (93184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93248_93311 :
    ∀ i : Fin 64, indexedBlockCheck (93248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93312_93375 :
    ∀ i : Fin 64, indexedBlockCheck (93312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93376_93439 :
    ∀ i : Fin 64, indexedBlockCheck (93376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93440_93503 :
    ∀ i : Fin 64, indexedBlockCheck (93440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93504_93567 :
    ∀ i : Fin 64, indexedBlockCheck (93504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93568_93631 :
    ∀ i : Fin 64, indexedBlockCheck (93568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93632_93695 :
    ∀ i : Fin 64, indexedBlockCheck (93632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93184_93695 :
    ∀ i : Fin 512, indexedBlockCheck (93184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93184 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 93184 0 64 h0 checkBlocks_93184_93247
  have h128 := extendCertifiedSegment 93184 64 64 h64 checkBlocks_93248_93311
  have h192 := extendCertifiedSegment 93184 128 64 h128 checkBlocks_93312_93375
  have h256 := extendCertifiedSegment 93184 192 64 h192 checkBlocks_93376_93439
  have h320 := extendCertifiedSegment 93184 256 64 h256 checkBlocks_93440_93503
  have h384 := extendCertifiedSegment 93184 320 64 h320 checkBlocks_93504_93567
  have h448 := extendCertifiedSegment 93184 384 64 h384 checkBlocks_93568_93631
  have h512 := extendCertifiedSegment 93184 448 64 h448 checkBlocks_93632_93695
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_93696_93759 :
    ∀ i : Fin 64, indexedBlockCheck (93696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93760_93823 :
    ∀ i : Fin 64, indexedBlockCheck (93760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93824_93887 :
    ∀ i : Fin 64, indexedBlockCheck (93824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93888_93951 :
    ∀ i : Fin 64, indexedBlockCheck (93888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93952_94015 :
    ∀ i : Fin 64, indexedBlockCheck (93952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94016_94079 :
    ∀ i : Fin 64, indexedBlockCheck (94016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94080_94143 :
    ∀ i : Fin 64, indexedBlockCheck (94080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94144_94207 :
    ∀ i : Fin 64, indexedBlockCheck (94144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_93696_94207 :
    ∀ i : Fin 512, indexedBlockCheck (93696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93696 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 93696 0 64 h0 checkBlocks_93696_93759
  have h128 := extendCertifiedSegment 93696 64 64 h64 checkBlocks_93760_93823
  have h192 := extendCertifiedSegment 93696 128 64 h128 checkBlocks_93824_93887
  have h256 := extendCertifiedSegment 93696 192 64 h192 checkBlocks_93888_93951
  have h320 := extendCertifiedSegment 93696 256 64 h256 checkBlocks_93952_94015
  have h384 := extendCertifiedSegment 93696 320 64 h320 checkBlocks_94016_94079
  have h448 := extendCertifiedSegment 93696 384 64 h384 checkBlocks_94080_94143
  have h512 := extendCertifiedSegment 93696 448 64 h448 checkBlocks_94144_94207
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_94208_94271 :
    ∀ i : Fin 64, indexedBlockCheck (94208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94272_94335 :
    ∀ i : Fin 64, indexedBlockCheck (94272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94336_94399 :
    ∀ i : Fin 64, indexedBlockCheck (94336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94400_94463 :
    ∀ i : Fin 64, indexedBlockCheck (94400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94464_94527 :
    ∀ i : Fin 64, indexedBlockCheck (94464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94528_94591 :
    ∀ i : Fin 64, indexedBlockCheck (94528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94592_94655 :
    ∀ i : Fin 64, indexedBlockCheck (94592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94656_94719 :
    ∀ i : Fin 64, indexedBlockCheck (94656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94208_94719 :
    ∀ i : Fin 512, indexedBlockCheck (94208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94208 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 94208 0 64 h0 checkBlocks_94208_94271
  have h128 := extendCertifiedSegment 94208 64 64 h64 checkBlocks_94272_94335
  have h192 := extendCertifiedSegment 94208 128 64 h128 checkBlocks_94336_94399
  have h256 := extendCertifiedSegment 94208 192 64 h192 checkBlocks_94400_94463
  have h320 := extendCertifiedSegment 94208 256 64 h256 checkBlocks_94464_94527
  have h384 := extendCertifiedSegment 94208 320 64 h320 checkBlocks_94528_94591
  have h448 := extendCertifiedSegment 94208 384 64 h384 checkBlocks_94592_94655
  have h512 := extendCertifiedSegment 94208 448 64 h448 checkBlocks_94656_94719
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_94720_94783 :
    ∀ i : Fin 64, indexedBlockCheck (94720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94784_94847 :
    ∀ i : Fin 64, indexedBlockCheck (94784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94848_94911 :
    ∀ i : Fin 64, indexedBlockCheck (94848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94912_94975 :
    ∀ i : Fin 64, indexedBlockCheck (94912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94976_95039 :
    ∀ i : Fin 64, indexedBlockCheck (94976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95040_95103 :
    ∀ i : Fin 64, indexedBlockCheck (95040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95104_95167 :
    ∀ i : Fin 64, indexedBlockCheck (95104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_95168_95231 :
    ∀ i : Fin 64, indexedBlockCheck (95168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_94720_95231 :
    ∀ i : Fin 512, indexedBlockCheck (94720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (94720 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 94720 0 64 h0 checkBlocks_94720_94783
  have h128 := extendCertifiedSegment 94720 64 64 h64 checkBlocks_94784_94847
  have h192 := extendCertifiedSegment 94720 128 64 h128 checkBlocks_94848_94911
  have h256 := extendCertifiedSegment 94720 192 64 h192 checkBlocks_94912_94975
  have h320 := extendCertifiedSegment 94720 256 64 h256 checkBlocks_94976_95039
  have h384 := extendCertifiedSegment 94720 320 64 h320 checkBlocks_95040_95103
  have h448 := extendCertifiedSegment 94720 384 64 h384 checkBlocks_95104_95167
  have h512 := extendCertifiedSegment 94720 448 64 h448 checkBlocks_95168_95231
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [93184, 95232) passes the packed checker. -/
public theorem blocks_in_93184_95232 :
    ∀ i : Fin 2048, indexedBlockCheck (93184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (93184 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 93184 0 512 h0 checkBlocks_93184_93695
  have h1024 := extendCertifiedSegment 93184 512 512 h512 checkBlocks_93696_94207
  have h1536 := extendCertifiedSegment 93184 1024 512 h1024 checkBlocks_94208_94719
  have h2048 := extendCertifiedSegment 93184 1536 512 h1536 checkBlocks_94720_95231
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
