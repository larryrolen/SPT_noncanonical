/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 27648 through 29695 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_27648_27711 :
    ∀ i : Fin 64, indexedBlockCheck (27648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27712_27775 :
    ∀ i : Fin 64, indexedBlockCheck (27712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27776_27839 :
    ∀ i : Fin 64, indexedBlockCheck (27776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27840_27903 :
    ∀ i : Fin 64, indexedBlockCheck (27840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27904_27967 :
    ∀ i : Fin 64, indexedBlockCheck (27904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27968_28031 :
    ∀ i : Fin 64, indexedBlockCheck (27968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28032_28095 :
    ∀ i : Fin 64, indexedBlockCheck (28032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28096_28159 :
    ∀ i : Fin 64, indexedBlockCheck (28096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27648_28159 :
    ∀ i : Fin 512, indexedBlockCheck (27648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27648 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 27648 0 64 h0 checkBlocks_27648_27711
  have h128 := extendCertifiedSegment 27648 64 64 h64 checkBlocks_27712_27775
  have h192 := extendCertifiedSegment 27648 128 64 h128 checkBlocks_27776_27839
  have h256 := extendCertifiedSegment 27648 192 64 h192 checkBlocks_27840_27903
  have h320 := extendCertifiedSegment 27648 256 64 h256 checkBlocks_27904_27967
  have h384 := extendCertifiedSegment 27648 320 64 h320 checkBlocks_27968_28031
  have h448 := extendCertifiedSegment 27648 384 64 h384 checkBlocks_28032_28095
  have h512 := extendCertifiedSegment 27648 448 64 h448 checkBlocks_28096_28159
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_28160_28223 :
    ∀ i : Fin 64, indexedBlockCheck (28160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28224_28287 :
    ∀ i : Fin 64, indexedBlockCheck (28224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28288_28351 :
    ∀ i : Fin 64, indexedBlockCheck (28288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28352_28415 :
    ∀ i : Fin 64, indexedBlockCheck (28352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28416_28479 :
    ∀ i : Fin 64, indexedBlockCheck (28416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28480_28543 :
    ∀ i : Fin 64, indexedBlockCheck (28480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28544_28607 :
    ∀ i : Fin 64, indexedBlockCheck (28544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28608_28671 :
    ∀ i : Fin 64, indexedBlockCheck (28608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28160_28671 :
    ∀ i : Fin 512, indexedBlockCheck (28160 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (28160 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 28160 0 64 h0 checkBlocks_28160_28223
  have h128 := extendCertifiedSegment 28160 64 64 h64 checkBlocks_28224_28287
  have h192 := extendCertifiedSegment 28160 128 64 h128 checkBlocks_28288_28351
  have h256 := extendCertifiedSegment 28160 192 64 h192 checkBlocks_28352_28415
  have h320 := extendCertifiedSegment 28160 256 64 h256 checkBlocks_28416_28479
  have h384 := extendCertifiedSegment 28160 320 64 h320 checkBlocks_28480_28543
  have h448 := extendCertifiedSegment 28160 384 64 h384 checkBlocks_28544_28607
  have h512 := extendCertifiedSegment 28160 448 64 h448 checkBlocks_28608_28671
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_28672_28735 :
    ∀ i : Fin 64, indexedBlockCheck (28672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28736_28799 :
    ∀ i : Fin 64, indexedBlockCheck (28736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28800_28863 :
    ∀ i : Fin 64, indexedBlockCheck (28800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28864_28927 :
    ∀ i : Fin 64, indexedBlockCheck (28864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28928_28991 :
    ∀ i : Fin 64, indexedBlockCheck (28928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28992_29055 :
    ∀ i : Fin 64, indexedBlockCheck (28992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29056_29119 :
    ∀ i : Fin 64, indexedBlockCheck (29056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29120_29183 :
    ∀ i : Fin 64, indexedBlockCheck (29120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_28672_29183 :
    ∀ i : Fin 512, indexedBlockCheck (28672 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (28672 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 28672 0 64 h0 checkBlocks_28672_28735
  have h128 := extendCertifiedSegment 28672 64 64 h64 checkBlocks_28736_28799
  have h192 := extendCertifiedSegment 28672 128 64 h128 checkBlocks_28800_28863
  have h256 := extendCertifiedSegment 28672 192 64 h192 checkBlocks_28864_28927
  have h320 := extendCertifiedSegment 28672 256 64 h256 checkBlocks_28928_28991
  have h384 := extendCertifiedSegment 28672 320 64 h320 checkBlocks_28992_29055
  have h448 := extendCertifiedSegment 28672 384 64 h384 checkBlocks_29056_29119
  have h512 := extendCertifiedSegment 28672 448 64 h448 checkBlocks_29120_29183
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_29184_29247 :
    ∀ i : Fin 64, indexedBlockCheck (29184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29248_29311 :
    ∀ i : Fin 64, indexedBlockCheck (29248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29312_29375 :
    ∀ i : Fin 64, indexedBlockCheck (29312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29376_29439 :
    ∀ i : Fin 64, indexedBlockCheck (29376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29440_29503 :
    ∀ i : Fin 64, indexedBlockCheck (29440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29504_29567 :
    ∀ i : Fin 64, indexedBlockCheck (29504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29568_29631 :
    ∀ i : Fin 64, indexedBlockCheck (29568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29632_29695 :
    ∀ i : Fin 64, indexedBlockCheck (29632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29184_29695 :
    ∀ i : Fin 512, indexedBlockCheck (29184 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (29184 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 29184 0 64 h0 checkBlocks_29184_29247
  have h128 := extendCertifiedSegment 29184 64 64 h64 checkBlocks_29248_29311
  have h192 := extendCertifiedSegment 29184 128 64 h128 checkBlocks_29312_29375
  have h256 := extendCertifiedSegment 29184 192 64 h192 checkBlocks_29376_29439
  have h320 := extendCertifiedSegment 29184 256 64 h256 checkBlocks_29440_29503
  have h384 := extendCertifiedSegment 29184 320 64 h320 checkBlocks_29504_29567
  have h448 := extendCertifiedSegment 29184 384 64 h384 checkBlocks_29568_29631
  have h512 := extendCertifiedSegment 29184 448 64 h448 checkBlocks_29632_29695
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [27648, 29696) passes the packed checker. -/
public theorem blocks_in_27648_29696 :
    ∀ i : Fin 2048, indexedBlockCheck (27648 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27648 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 27648 0 512 h0 checkBlocks_27648_28159
  have h1024 := extendCertifiedSegment 27648 512 512 h512 checkBlocks_28160_28671
  have h1536 := extendCertifiedSegment 27648 1024 512 h1024 checkBlocks_28672_29183
  have h2048 := extendCertifiedSegment 27648 1536 512 h1536 checkBlocks_29184_29695
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
