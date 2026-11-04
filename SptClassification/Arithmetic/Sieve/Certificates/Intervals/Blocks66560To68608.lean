/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 66560 through 68607 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_66560_66623 :
    ∀ i : Fin 64, indexedBlockCheck (66560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66624_66687 :
    ∀ i : Fin 64, indexedBlockCheck (66624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66688_66751 :
    ∀ i : Fin 64, indexedBlockCheck (66688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66752_66815 :
    ∀ i : Fin 64, indexedBlockCheck (66752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66816_66879 :
    ∀ i : Fin 64, indexedBlockCheck (66816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66880_66943 :
    ∀ i : Fin 64, indexedBlockCheck (66880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66944_67007 :
    ∀ i : Fin 64, indexedBlockCheck (66944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67008_67071 :
    ∀ i : Fin 64, indexedBlockCheck (67008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_66560_67071 :
    ∀ i : Fin 512, indexedBlockCheck (66560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66560 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 66560 0 64 h0 checkBlocks_66560_66623
  have h128 := extendCertifiedSegment 66560 64 64 h64 checkBlocks_66624_66687
  have h192 := extendCertifiedSegment 66560 128 64 h128 checkBlocks_66688_66751
  have h256 := extendCertifiedSegment 66560 192 64 h192 checkBlocks_66752_66815
  have h320 := extendCertifiedSegment 66560 256 64 h256 checkBlocks_66816_66879
  have h384 := extendCertifiedSegment 66560 320 64 h320 checkBlocks_66880_66943
  have h448 := extendCertifiedSegment 66560 384 64 h384 checkBlocks_66944_67007
  have h512 := extendCertifiedSegment 66560 448 64 h448 checkBlocks_67008_67071
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_67072_67135 :
    ∀ i : Fin 64, indexedBlockCheck (67072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67136_67199 :
    ∀ i : Fin 64, indexedBlockCheck (67136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67200_67263 :
    ∀ i : Fin 64, indexedBlockCheck (67200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67264_67327 :
    ∀ i : Fin 64, indexedBlockCheck (67264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67328_67391 :
    ∀ i : Fin 64, indexedBlockCheck (67328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67392_67455 :
    ∀ i : Fin 64, indexedBlockCheck (67392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67456_67519 :
    ∀ i : Fin 64, indexedBlockCheck (67456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67520_67583 :
    ∀ i : Fin 64, indexedBlockCheck (67520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67072_67583 :
    ∀ i : Fin 512, indexedBlockCheck (67072 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67072 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 67072 0 64 h0 checkBlocks_67072_67135
  have h128 := extendCertifiedSegment 67072 64 64 h64 checkBlocks_67136_67199
  have h192 := extendCertifiedSegment 67072 128 64 h128 checkBlocks_67200_67263
  have h256 := extendCertifiedSegment 67072 192 64 h192 checkBlocks_67264_67327
  have h320 := extendCertifiedSegment 67072 256 64 h256 checkBlocks_67328_67391
  have h384 := extendCertifiedSegment 67072 320 64 h320 checkBlocks_67392_67455
  have h448 := extendCertifiedSegment 67072 384 64 h384 checkBlocks_67456_67519
  have h512 := extendCertifiedSegment 67072 448 64 h448 checkBlocks_67520_67583
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_67584_67647 :
    ∀ i : Fin 64, indexedBlockCheck (67584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67648_67711 :
    ∀ i : Fin 64, indexedBlockCheck (67648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67712_67775 :
    ∀ i : Fin 64, indexedBlockCheck (67712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67776_67839 :
    ∀ i : Fin 64, indexedBlockCheck (67776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67840_67903 :
    ∀ i : Fin 64, indexedBlockCheck (67840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67904_67967 :
    ∀ i : Fin 64, indexedBlockCheck (67904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67968_68031 :
    ∀ i : Fin 64, indexedBlockCheck (67968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68032_68095 :
    ∀ i : Fin 64, indexedBlockCheck (68032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_67584_68095 :
    ∀ i : Fin 512, indexedBlockCheck (67584 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (67584 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 67584 0 64 h0 checkBlocks_67584_67647
  have h128 := extendCertifiedSegment 67584 64 64 h64 checkBlocks_67648_67711
  have h192 := extendCertifiedSegment 67584 128 64 h128 checkBlocks_67712_67775
  have h256 := extendCertifiedSegment 67584 192 64 h192 checkBlocks_67776_67839
  have h320 := extendCertifiedSegment 67584 256 64 h256 checkBlocks_67840_67903
  have h384 := extendCertifiedSegment 67584 320 64 h320 checkBlocks_67904_67967
  have h448 := extendCertifiedSegment 67584 384 64 h384 checkBlocks_67968_68031
  have h512 := extendCertifiedSegment 67584 448 64 h448 checkBlocks_68032_68095
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_68096_68159 :
    ∀ i : Fin 64, indexedBlockCheck (68096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68160_68223 :
    ∀ i : Fin 64, indexedBlockCheck (68160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68224_68287 :
    ∀ i : Fin 64, indexedBlockCheck (68224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68288_68351 :
    ∀ i : Fin 64, indexedBlockCheck (68288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68352_68415 :
    ∀ i : Fin 64, indexedBlockCheck (68352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68416_68479 :
    ∀ i : Fin 64, indexedBlockCheck (68416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68480_68543 :
    ∀ i : Fin 64, indexedBlockCheck (68480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68544_68607 :
    ∀ i : Fin 64, indexedBlockCheck (68544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68096_68607 :
    ∀ i : Fin 512, indexedBlockCheck (68096 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68096 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 68096 0 64 h0 checkBlocks_68096_68159
  have h128 := extendCertifiedSegment 68096 64 64 h64 checkBlocks_68160_68223
  have h192 := extendCertifiedSegment 68096 128 64 h128 checkBlocks_68224_68287
  have h256 := extendCertifiedSegment 68096 192 64 h192 checkBlocks_68288_68351
  have h320 := extendCertifiedSegment 68096 256 64 h256 checkBlocks_68352_68415
  have h384 := extendCertifiedSegment 68096 320 64 h320 checkBlocks_68416_68479
  have h448 := extendCertifiedSegment 68096 384 64 h384 checkBlocks_68480_68543
  have h512 := extendCertifiedSegment 68096 448 64 h448 checkBlocks_68544_68607
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [66560, 68608) passes the packed checker. -/
public theorem blocks_in_66560_68608 :
    ∀ i : Fin 2048, indexedBlockCheck (66560 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (66560 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 66560 0 512 h0 checkBlocks_66560_67071
  have h1024 := extendCertifiedSegment 66560 512 512 h512 checkBlocks_67072_67583
  have h1536 := extendCertifiedSegment 66560 1024 512 h1024 checkBlocks_67584_68095
  have h2048 := extendCertifiedSegment 66560 1536 512 h1536 checkBlocks_68096_68607
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
