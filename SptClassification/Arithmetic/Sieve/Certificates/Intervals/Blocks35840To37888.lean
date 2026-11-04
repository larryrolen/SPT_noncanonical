/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks31744To33792

/-! # Certified checker blocks from 35840 through 37887 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_35840_35903 :
    ∀ i : Fin 64, indexedBlockCheck (35840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35904_35967 :
    ∀ i : Fin 64, indexedBlockCheck (35904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35968_36031 :
    ∀ i : Fin 64, indexedBlockCheck (35968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36032_36095 :
    ∀ i : Fin 64, indexedBlockCheck (36032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36096_36159 :
    ∀ i : Fin 64, indexedBlockCheck (36096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36160_36223 :
    ∀ i : Fin 64, indexedBlockCheck (36160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36224_36287 :
    ∀ i : Fin 64, indexedBlockCheck (36224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36288_36351 :
    ∀ i : Fin 64, indexedBlockCheck (36288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_35840_36351 :
    ∀ i : Fin 512, indexedBlockCheck (35840 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35840 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 35840 0 64 h0 checkBlocks_35840_35903
  have h128 := extendCertifiedSegment 35840 64 64 h64 checkBlocks_35904_35967
  have h192 := extendCertifiedSegment 35840 128 64 h128 checkBlocks_35968_36031
  have h256 := extendCertifiedSegment 35840 192 64 h192 checkBlocks_36032_36095
  have h320 := extendCertifiedSegment 35840 256 64 h256 checkBlocks_36096_36159
  have h384 := extendCertifiedSegment 35840 320 64 h320 checkBlocks_36160_36223
  have h448 := extendCertifiedSegment 35840 384 64 h384 checkBlocks_36224_36287
  have h512 := extendCertifiedSegment 35840 448 64 h448 checkBlocks_36288_36351
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_36352_36415 :
    ∀ i : Fin 64, indexedBlockCheck (36352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36416_36479 :
    ∀ i : Fin 64, indexedBlockCheck (36416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36480_36543 :
    ∀ i : Fin 64, indexedBlockCheck (36480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36544_36607 :
    ∀ i : Fin 64, indexedBlockCheck (36544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36608_36671 :
    ∀ i : Fin 64, indexedBlockCheck (36608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36672_36735 :
    ∀ i : Fin 64, indexedBlockCheck (36672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36736_36799 :
    ∀ i : Fin 64, indexedBlockCheck (36736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36800_36863 :
    ∀ i : Fin 64, indexedBlockCheck (36800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36352_36863 :
    ∀ i : Fin 512, indexedBlockCheck (36352 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (36352 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 36352 0 64 h0 checkBlocks_36352_36415
  have h128 := extendCertifiedSegment 36352 64 64 h64 checkBlocks_36416_36479
  have h192 := extendCertifiedSegment 36352 128 64 h128 checkBlocks_36480_36543
  have h256 := extendCertifiedSegment 36352 192 64 h192 checkBlocks_36544_36607
  have h320 := extendCertifiedSegment 36352 256 64 h256 checkBlocks_36608_36671
  have h384 := extendCertifiedSegment 36352 320 64 h320 checkBlocks_36672_36735
  have h448 := extendCertifiedSegment 36352 384 64 h384 checkBlocks_36736_36799
  have h512 := extendCertifiedSegment 36352 448 64 h448 checkBlocks_36800_36863
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_36864_36927 :
    ∀ i : Fin 64, indexedBlockCheck (36864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36928_36991 :
    ∀ i : Fin 64, indexedBlockCheck (36928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36992_37055 :
    ∀ i : Fin 64, indexedBlockCheck (36992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37056_37119 :
    ∀ i : Fin 64, indexedBlockCheck (37056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37120_37183 :
    ∀ i : Fin 64, indexedBlockCheck (37120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37184_37247 :
    ∀ i : Fin 64, indexedBlockCheck (37184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37248_37311 :
    ∀ i : Fin 64, indexedBlockCheck (37248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37312_37375 :
    ∀ i : Fin 64, indexedBlockCheck (37312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_36864_37375 :
    ∀ i : Fin 512, indexedBlockCheck (36864 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (36864 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 36864 0 64 h0 checkBlocks_36864_36927
  have h128 := extendCertifiedSegment 36864 64 64 h64 checkBlocks_36928_36991
  have h192 := extendCertifiedSegment 36864 128 64 h128 checkBlocks_36992_37055
  have h256 := extendCertifiedSegment 36864 192 64 h192 checkBlocks_37056_37119
  have h320 := extendCertifiedSegment 36864 256 64 h256 checkBlocks_37120_37183
  have h384 := extendCertifiedSegment 36864 320 64 h320 checkBlocks_37184_37247
  have h448 := extendCertifiedSegment 36864 384 64 h384 checkBlocks_37248_37311
  have h512 := extendCertifiedSegment 36864 448 64 h448 checkBlocks_37312_37375
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_37376_37439 :
    ∀ i : Fin 64, indexedBlockCheck (37376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37440_37503 :
    ∀ i : Fin 64, indexedBlockCheck (37440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37504_37567 :
    ∀ i : Fin 64, indexedBlockCheck (37504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37568_37631 :
    ∀ i : Fin 64, indexedBlockCheck (37568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37632_37695 :
    ∀ i : Fin 64, indexedBlockCheck (37632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37696_37759 :
    ∀ i : Fin 64, indexedBlockCheck (37696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37760_37823 :
    ∀ i : Fin 64, indexedBlockCheck (37760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37824_37887 :
    ∀ i : Fin 64, indexedBlockCheck (37824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_37376_37887 :
    ∀ i : Fin 512, indexedBlockCheck (37376 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (37376 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 37376 0 64 h0 checkBlocks_37376_37439
  have h128 := extendCertifiedSegment 37376 64 64 h64 checkBlocks_37440_37503
  have h192 := extendCertifiedSegment 37376 128 64 h128 checkBlocks_37504_37567
  have h256 := extendCertifiedSegment 37376 192 64 h192 checkBlocks_37568_37631
  have h320 := extendCertifiedSegment 37376 256 64 h256 checkBlocks_37632_37695
  have h384 := extendCertifiedSegment 37376 320 64 h320 checkBlocks_37696_37759
  have h448 := extendCertifiedSegment 37376 384 64 h384 checkBlocks_37760_37823
  have h512 := extendCertifiedSegment 37376 448 64 h448 checkBlocks_37824_37887
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [35840, 37888) passes the packed checker. -/
public theorem blocks_in_35840_37888 :
    ∀ i : Fin 2048, indexedBlockCheck (35840 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (35840 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 35840 0 512 h0 checkBlocks_35840_36351
  have h1024 := extendCertifiedSegment 35840 512 512 h512 checkBlocks_36352_36863
  have h1536 := extendCertifiedSegment 35840 1024 512 h1024 checkBlocks_36864_37375
  have h2048 := extendCertifiedSegment 35840 1536 512 h1536 checkBlocks_37376_37887
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
