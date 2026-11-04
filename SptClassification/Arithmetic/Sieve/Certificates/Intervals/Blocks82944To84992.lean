/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks78848To80896

/-! # Certified checker blocks from 82944 through 84991 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_82944_83007 :
    ∀ i : Fin 64, indexedBlockCheck (82944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83008_83071 :
    ∀ i : Fin 64, indexedBlockCheck (83008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83072_83135 :
    ∀ i : Fin 64, indexedBlockCheck (83072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83136_83199 :
    ∀ i : Fin 64, indexedBlockCheck (83136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83200_83263 :
    ∀ i : Fin 64, indexedBlockCheck (83200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83264_83327 :
    ∀ i : Fin 64, indexedBlockCheck (83264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83328_83391 :
    ∀ i : Fin 64, indexedBlockCheck (83328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83392_83455 :
    ∀ i : Fin 64, indexedBlockCheck (83392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_82944_83455 :
    ∀ i : Fin 512, indexedBlockCheck (82944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82944 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 82944 0 64 h0 checkBlocks_82944_83007
  have h128 := extendCertifiedSegment 82944 64 64 h64 checkBlocks_83008_83071
  have h192 := extendCertifiedSegment 82944 128 64 h128 checkBlocks_83072_83135
  have h256 := extendCertifiedSegment 82944 192 64 h192 checkBlocks_83136_83199
  have h320 := extendCertifiedSegment 82944 256 64 h256 checkBlocks_83200_83263
  have h384 := extendCertifiedSegment 82944 320 64 h320 checkBlocks_83264_83327
  have h448 := extendCertifiedSegment 82944 384 64 h384 checkBlocks_83328_83391
  have h512 := extendCertifiedSegment 82944 448 64 h448 checkBlocks_83392_83455
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_83456_83519 :
    ∀ i : Fin 64, indexedBlockCheck (83456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83520_83583 :
    ∀ i : Fin 64, indexedBlockCheck (83520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83584_83647 :
    ∀ i : Fin 64, indexedBlockCheck (83584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83648_83711 :
    ∀ i : Fin 64, indexedBlockCheck (83648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83712_83775 :
    ∀ i : Fin 64, indexedBlockCheck (83712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83776_83839 :
    ∀ i : Fin 64, indexedBlockCheck (83776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83840_83903 :
    ∀ i : Fin 64, indexedBlockCheck (83840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83904_83967 :
    ∀ i : Fin 64, indexedBlockCheck (83904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83456_83967 :
    ∀ i : Fin 512, indexedBlockCheck (83456 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83456 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 83456 0 64 h0 checkBlocks_83456_83519
  have h128 := extendCertifiedSegment 83456 64 64 h64 checkBlocks_83520_83583
  have h192 := extendCertifiedSegment 83456 128 64 h128 checkBlocks_83584_83647
  have h256 := extendCertifiedSegment 83456 192 64 h192 checkBlocks_83648_83711
  have h320 := extendCertifiedSegment 83456 256 64 h256 checkBlocks_83712_83775
  have h384 := extendCertifiedSegment 83456 320 64 h320 checkBlocks_83776_83839
  have h448 := extendCertifiedSegment 83456 384 64 h384 checkBlocks_83840_83903
  have h512 := extendCertifiedSegment 83456 448 64 h448 checkBlocks_83904_83967
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_83968_84031 :
    ∀ i : Fin 64, indexedBlockCheck (83968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84032_84095 :
    ∀ i : Fin 64, indexedBlockCheck (84032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84096_84159 :
    ∀ i : Fin 64, indexedBlockCheck (84096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84160_84223 :
    ∀ i : Fin 64, indexedBlockCheck (84160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84224_84287 :
    ∀ i : Fin 64, indexedBlockCheck (84224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84288_84351 :
    ∀ i : Fin 64, indexedBlockCheck (84288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84352_84415 :
    ∀ i : Fin 64, indexedBlockCheck (84352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84416_84479 :
    ∀ i : Fin 64, indexedBlockCheck (84416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_83968_84479 :
    ∀ i : Fin 512, indexedBlockCheck (83968 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (83968 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 83968 0 64 h0 checkBlocks_83968_84031
  have h128 := extendCertifiedSegment 83968 64 64 h64 checkBlocks_84032_84095
  have h192 := extendCertifiedSegment 83968 128 64 h128 checkBlocks_84096_84159
  have h256 := extendCertifiedSegment 83968 192 64 h192 checkBlocks_84160_84223
  have h320 := extendCertifiedSegment 83968 256 64 h256 checkBlocks_84224_84287
  have h384 := extendCertifiedSegment 83968 320 64 h320 checkBlocks_84288_84351
  have h448 := extendCertifiedSegment 83968 384 64 h384 checkBlocks_84352_84415
  have h512 := extendCertifiedSegment 83968 448 64 h448 checkBlocks_84416_84479
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_84480_84543 :
    ∀ i : Fin 64, indexedBlockCheck (84480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84544_84607 :
    ∀ i : Fin 64, indexedBlockCheck (84544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84608_84671 :
    ∀ i : Fin 64, indexedBlockCheck (84608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84672_84735 :
    ∀ i : Fin 64, indexedBlockCheck (84672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84736_84799 :
    ∀ i : Fin 64, indexedBlockCheck (84736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84800_84863 :
    ∀ i : Fin 64, indexedBlockCheck (84800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84864_84927 :
    ∀ i : Fin 64, indexedBlockCheck (84864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84928_84991 :
    ∀ i : Fin 64, indexedBlockCheck (84928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_84480_84991 :
    ∀ i : Fin 512, indexedBlockCheck (84480 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (84480 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 84480 0 64 h0 checkBlocks_84480_84543
  have h128 := extendCertifiedSegment 84480 64 64 h64 checkBlocks_84544_84607
  have h192 := extendCertifiedSegment 84480 128 64 h128 checkBlocks_84608_84671
  have h256 := extendCertifiedSegment 84480 192 64 h192 checkBlocks_84672_84735
  have h320 := extendCertifiedSegment 84480 256 64 h256 checkBlocks_84736_84799
  have h384 := extendCertifiedSegment 84480 320 64 h320 checkBlocks_84800_84863
  have h448 := extendCertifiedSegment 84480 384 64 h384 checkBlocks_84864_84927
  have h512 := extendCertifiedSegment 84480 448 64 h448 checkBlocks_84928_84991
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [82944, 84992) passes the packed checker. -/
public theorem blocks_in_82944_84992 :
    ∀ i : Fin 2048, indexedBlockCheck (82944 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (82944 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 82944 0 512 h0 checkBlocks_82944_83455
  have h1024 := extendCertifiedSegment 82944 512 512 h512 checkBlocks_83456_83967
  have h1536 := extendCertifiedSegment 82944 1024 512 h1024 checkBlocks_83968_84479
  have h2048 := extendCertifiedSegment 82944 1536 512 h1536 checkBlocks_84480_84991
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
