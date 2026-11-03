/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 13312 through 15359 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_13312_13375 :
    ∀ i : Fin 64, indexedBlockCheck (13312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13376_13439 :
    ∀ i : Fin 64, indexedBlockCheck (13376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13440_13503 :
    ∀ i : Fin 64, indexedBlockCheck (13440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13504_13567 :
    ∀ i : Fin 64, indexedBlockCheck (13504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13568_13631 :
    ∀ i : Fin 64, indexedBlockCheck (13568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13632_13695 :
    ∀ i : Fin 64, indexedBlockCheck (13632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13696_13759 :
    ∀ i : Fin 64, indexedBlockCheck (13696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13760_13823 :
    ∀ i : Fin 64, indexedBlockCheck (13760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13312_13823 :
    ∀ i : Fin 512, indexedBlockCheck (13312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (13312 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 13312 0 64 h0 checkBlocks_13312_13375
  have h128 := extendCertifiedSegment 13312 64 64 h64 checkBlocks_13376_13439
  have h192 := extendCertifiedSegment 13312 128 64 h128 checkBlocks_13440_13503
  have h256 := extendCertifiedSegment 13312 192 64 h192 checkBlocks_13504_13567
  have h320 := extendCertifiedSegment 13312 256 64 h256 checkBlocks_13568_13631
  have h384 := extendCertifiedSegment 13312 320 64 h320 checkBlocks_13632_13695
  have h448 := extendCertifiedSegment 13312 384 64 h384 checkBlocks_13696_13759
  have h512 := extendCertifiedSegment 13312 448 64 h448 checkBlocks_13760_13823
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_13824_13887 :
    ∀ i : Fin 64, indexedBlockCheck (13824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13888_13951 :
    ∀ i : Fin 64, indexedBlockCheck (13888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13952_14015 :
    ∀ i : Fin 64, indexedBlockCheck (13952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14016_14079 :
    ∀ i : Fin 64, indexedBlockCheck (14016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14080_14143 :
    ∀ i : Fin 64, indexedBlockCheck (14080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14144_14207 :
    ∀ i : Fin 64, indexedBlockCheck (14144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14208_14271 :
    ∀ i : Fin 64, indexedBlockCheck (14208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14272_14335 :
    ∀ i : Fin 64, indexedBlockCheck (14272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_13824_14335 :
    ∀ i : Fin 512, indexedBlockCheck (13824 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (13824 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 13824 0 64 h0 checkBlocks_13824_13887
  have h128 := extendCertifiedSegment 13824 64 64 h64 checkBlocks_13888_13951
  have h192 := extendCertifiedSegment 13824 128 64 h128 checkBlocks_13952_14015
  have h256 := extendCertifiedSegment 13824 192 64 h192 checkBlocks_14016_14079
  have h320 := extendCertifiedSegment 13824 256 64 h256 checkBlocks_14080_14143
  have h384 := extendCertifiedSegment 13824 320 64 h320 checkBlocks_14144_14207
  have h448 := extendCertifiedSegment 13824 384 64 h384 checkBlocks_14208_14271
  have h512 := extendCertifiedSegment 13824 448 64 h448 checkBlocks_14272_14335
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_14336_14399 :
    ∀ i : Fin 64, indexedBlockCheck (14336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14400_14463 :
    ∀ i : Fin 64, indexedBlockCheck (14400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14464_14527 :
    ∀ i : Fin 64, indexedBlockCheck (14464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14528_14591 :
    ∀ i : Fin 64, indexedBlockCheck (14528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14592_14655 :
    ∀ i : Fin 64, indexedBlockCheck (14592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14656_14719 :
    ∀ i : Fin 64, indexedBlockCheck (14656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14720_14783 :
    ∀ i : Fin 64, indexedBlockCheck (14720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14784_14847 :
    ∀ i : Fin 64, indexedBlockCheck (14784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14336_14847 :
    ∀ i : Fin 512, indexedBlockCheck (14336 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (14336 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 14336 0 64 h0 checkBlocks_14336_14399
  have h128 := extendCertifiedSegment 14336 64 64 h64 checkBlocks_14400_14463
  have h192 := extendCertifiedSegment 14336 128 64 h128 checkBlocks_14464_14527
  have h256 := extendCertifiedSegment 14336 192 64 h192 checkBlocks_14528_14591
  have h320 := extendCertifiedSegment 14336 256 64 h256 checkBlocks_14592_14655
  have h384 := extendCertifiedSegment 14336 320 64 h320 checkBlocks_14656_14719
  have h448 := extendCertifiedSegment 14336 384 64 h384 checkBlocks_14720_14783
  have h512 := extendCertifiedSegment 14336 448 64 h448 checkBlocks_14784_14847
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_14848_14911 :
    ∀ i : Fin 64, indexedBlockCheck (14848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14912_14975 :
    ∀ i : Fin 64, indexedBlockCheck (14912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14976_15039 :
    ∀ i : Fin 64, indexedBlockCheck (14976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15040_15103 :
    ∀ i : Fin 64, indexedBlockCheck (15040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15104_15167 :
    ∀ i : Fin 64, indexedBlockCheck (15104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15168_15231 :
    ∀ i : Fin 64, indexedBlockCheck (15168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15232_15295 :
    ∀ i : Fin 64, indexedBlockCheck (15232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_15296_15359 :
    ∀ i : Fin 64, indexedBlockCheck (15296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_14848_15359 :
    ∀ i : Fin 512, indexedBlockCheck (14848 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (14848 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 14848 0 64 h0 checkBlocks_14848_14911
  have h128 := extendCertifiedSegment 14848 64 64 h64 checkBlocks_14912_14975
  have h192 := extendCertifiedSegment 14848 128 64 h128 checkBlocks_14976_15039
  have h256 := extendCertifiedSegment 14848 192 64 h192 checkBlocks_15040_15103
  have h320 := extendCertifiedSegment 14848 256 64 h256 checkBlocks_15104_15167
  have h384 := extendCertifiedSegment 14848 320 64 h320 checkBlocks_15168_15231
  have h448 := extendCertifiedSegment 14848 384 64 h384 checkBlocks_15232_15295
  have h512 := extendCertifiedSegment 14848 448 64 h448 checkBlocks_15296_15359
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [13312, 15360) passes the packed checker. -/
public theorem blocks_in_13312_15360 :
    ∀ i : Fin 2048, indexedBlockCheck (13312 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (13312 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 13312 0 512 h0 checkBlocks_13312_13823
  have h1024 := extendCertifiedSegment 13312 512 512 h512 checkBlocks_13824_14335
  have h1536 := extendCertifiedSegment 13312 1024 512 h1024 checkBlocks_14336_14847
  have h2048 := extendCertifiedSegment 13312 1536 512 h1536 checkBlocks_14848_15359
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
