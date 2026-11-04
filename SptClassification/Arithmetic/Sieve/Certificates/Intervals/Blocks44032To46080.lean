/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 44032 through 46079 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_44032_44095 :
    ∀ i : Fin 64, indexedBlockCheck (44032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44096_44159 :
    ∀ i : Fin 64, indexedBlockCheck (44096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44160_44223 :
    ∀ i : Fin 64, indexedBlockCheck (44160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44224_44287 :
    ∀ i : Fin 64, indexedBlockCheck (44224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44288_44351 :
    ∀ i : Fin 64, indexedBlockCheck (44288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44352_44415 :
    ∀ i : Fin 64, indexedBlockCheck (44352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44416_44479 :
    ∀ i : Fin 64, indexedBlockCheck (44416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44480_44543 :
    ∀ i : Fin 64, indexedBlockCheck (44480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44032_44543 :
    ∀ i : Fin 512, indexedBlockCheck (44032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44032 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 44032 0 64 h0 checkBlocks_44032_44095
  have h128 := extendCertifiedSegment 44032 64 64 h64 checkBlocks_44096_44159
  have h192 := extendCertifiedSegment 44032 128 64 h128 checkBlocks_44160_44223
  have h256 := extendCertifiedSegment 44032 192 64 h192 checkBlocks_44224_44287
  have h320 := extendCertifiedSegment 44032 256 64 h256 checkBlocks_44288_44351
  have h384 := extendCertifiedSegment 44032 320 64 h320 checkBlocks_44352_44415
  have h448 := extendCertifiedSegment 44032 384 64 h384 checkBlocks_44416_44479
  have h512 := extendCertifiedSegment 44032 448 64 h448 checkBlocks_44480_44543
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_44544_44607 :
    ∀ i : Fin 64, indexedBlockCheck (44544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44608_44671 :
    ∀ i : Fin 64, indexedBlockCheck (44608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44672_44735 :
    ∀ i : Fin 64, indexedBlockCheck (44672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44736_44799 :
    ∀ i : Fin 64, indexedBlockCheck (44736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44800_44863 :
    ∀ i : Fin 64, indexedBlockCheck (44800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44864_44927 :
    ∀ i : Fin 64, indexedBlockCheck (44864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44928_44991 :
    ∀ i : Fin 64, indexedBlockCheck (44928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44992_45055 :
    ∀ i : Fin 64, indexedBlockCheck (44992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_44544_45055 :
    ∀ i : Fin 512, indexedBlockCheck (44544 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44544 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 44544 0 64 h0 checkBlocks_44544_44607
  have h128 := extendCertifiedSegment 44544 64 64 h64 checkBlocks_44608_44671
  have h192 := extendCertifiedSegment 44544 128 64 h128 checkBlocks_44672_44735
  have h256 := extendCertifiedSegment 44544 192 64 h192 checkBlocks_44736_44799
  have h320 := extendCertifiedSegment 44544 256 64 h256 checkBlocks_44800_44863
  have h384 := extendCertifiedSegment 44544 320 64 h320 checkBlocks_44864_44927
  have h448 := extendCertifiedSegment 44544 384 64 h384 checkBlocks_44928_44991
  have h512 := extendCertifiedSegment 44544 448 64 h448 checkBlocks_44992_45055
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_45056_45119 :
    ∀ i : Fin 64, indexedBlockCheck (45056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45120_45183 :
    ∀ i : Fin 64, indexedBlockCheck (45120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45184_45247 :
    ∀ i : Fin 64, indexedBlockCheck (45184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45248_45311 :
    ∀ i : Fin 64, indexedBlockCheck (45248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45312_45375 :
    ∀ i : Fin 64, indexedBlockCheck (45312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45376_45439 :
    ∀ i : Fin 64, indexedBlockCheck (45376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45440_45503 :
    ∀ i : Fin 64, indexedBlockCheck (45440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45504_45567 :
    ∀ i : Fin 64, indexedBlockCheck (45504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45056_45567 :
    ∀ i : Fin 512, indexedBlockCheck (45056 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45056 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 45056 0 64 h0 checkBlocks_45056_45119
  have h128 := extendCertifiedSegment 45056 64 64 h64 checkBlocks_45120_45183
  have h192 := extendCertifiedSegment 45056 128 64 h128 checkBlocks_45184_45247
  have h256 := extendCertifiedSegment 45056 192 64 h192 checkBlocks_45248_45311
  have h320 := extendCertifiedSegment 45056 256 64 h256 checkBlocks_45312_45375
  have h384 := extendCertifiedSegment 45056 320 64 h320 checkBlocks_45376_45439
  have h448 := extendCertifiedSegment 45056 384 64 h384 checkBlocks_45440_45503
  have h512 := extendCertifiedSegment 45056 448 64 h448 checkBlocks_45504_45567
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_45568_45631 :
    ∀ i : Fin 64, indexedBlockCheck (45568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45632_45695 :
    ∀ i : Fin 64, indexedBlockCheck (45632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45696_45759 :
    ∀ i : Fin 64, indexedBlockCheck (45696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45760_45823 :
    ∀ i : Fin 64, indexedBlockCheck (45760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45824_45887 :
    ∀ i : Fin 64, indexedBlockCheck (45824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45888_45951 :
    ∀ i : Fin 64, indexedBlockCheck (45888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45952_46015 :
    ∀ i : Fin 64, indexedBlockCheck (45952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_46016_46079 :
    ∀ i : Fin 64, indexedBlockCheck (46016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_45568_46079 :
    ∀ i : Fin 512, indexedBlockCheck (45568 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (45568 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 45568 0 64 h0 checkBlocks_45568_45631
  have h128 := extendCertifiedSegment 45568 64 64 h64 checkBlocks_45632_45695
  have h192 := extendCertifiedSegment 45568 128 64 h128 checkBlocks_45696_45759
  have h256 := extendCertifiedSegment 45568 192 64 h192 checkBlocks_45760_45823
  have h320 := extendCertifiedSegment 45568 256 64 h256 checkBlocks_45824_45887
  have h384 := extendCertifiedSegment 45568 320 64 h320 checkBlocks_45888_45951
  have h448 := extendCertifiedSegment 45568 384 64 h384 checkBlocks_45952_46015
  have h512 := extendCertifiedSegment 45568 448 64 h448 checkBlocks_46016_46079
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [44032, 46080) passes the packed checker. -/
public theorem blocks_in_44032_46080 :
    ∀ i : Fin 2048, indexedBlockCheck (44032 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (44032 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 44032 0 512 h0 checkBlocks_44032_44543
  have h1024 := extendCertifiedSegment 44032 512 512 h512 checkBlocks_44544_45055
  have h1536 := extendCertifiedSegment 44032 1024 512 h1024 checkBlocks_45056_45567
  have h2048 := extendCertifiedSegment 44032 1536 512 h1536 checkBlocks_45568_46079
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
