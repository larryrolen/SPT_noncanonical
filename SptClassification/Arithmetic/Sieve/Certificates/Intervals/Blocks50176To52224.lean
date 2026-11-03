/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 50176 through 52223 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_50176_50239 :
    ∀ i : Fin 64, indexedBlockCheck (50176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50240_50303 :
    ∀ i : Fin 64, indexedBlockCheck (50240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50304_50367 :
    ∀ i : Fin 64, indexedBlockCheck (50304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50368_50431 :
    ∀ i : Fin 64, indexedBlockCheck (50368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50432_50495 :
    ∀ i : Fin 64, indexedBlockCheck (50432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50496_50559 :
    ∀ i : Fin 64, indexedBlockCheck (50496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50560_50623 :
    ∀ i : Fin 64, indexedBlockCheck (50560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50624_50687 :
    ∀ i : Fin 64, indexedBlockCheck (50624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50176_50687 :
    ∀ i : Fin 512, indexedBlockCheck (50176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (50176 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 50176 0 64 h0 checkBlocks_50176_50239
  have h128 := extendCertifiedSegment 50176 64 64 h64 checkBlocks_50240_50303
  have h192 := extendCertifiedSegment 50176 128 64 h128 checkBlocks_50304_50367
  have h256 := extendCertifiedSegment 50176 192 64 h192 checkBlocks_50368_50431
  have h320 := extendCertifiedSegment 50176 256 64 h256 checkBlocks_50432_50495
  have h384 := extendCertifiedSegment 50176 320 64 h320 checkBlocks_50496_50559
  have h448 := extendCertifiedSegment 50176 384 64 h384 checkBlocks_50560_50623
  have h512 := extendCertifiedSegment 50176 448 64 h448 checkBlocks_50624_50687
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_50688_50751 :
    ∀ i : Fin 64, indexedBlockCheck (50688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50752_50815 :
    ∀ i : Fin 64, indexedBlockCheck (50752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50816_50879 :
    ∀ i : Fin 64, indexedBlockCheck (50816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50880_50943 :
    ∀ i : Fin 64, indexedBlockCheck (50880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50944_51007 :
    ∀ i : Fin 64, indexedBlockCheck (50944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51008_51071 :
    ∀ i : Fin 64, indexedBlockCheck (51008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51072_51135 :
    ∀ i : Fin 64, indexedBlockCheck (51072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51136_51199 :
    ∀ i : Fin 64, indexedBlockCheck (51136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_50688_51199 :
    ∀ i : Fin 512, indexedBlockCheck (50688 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (50688 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 50688 0 64 h0 checkBlocks_50688_50751
  have h128 := extendCertifiedSegment 50688 64 64 h64 checkBlocks_50752_50815
  have h192 := extendCertifiedSegment 50688 128 64 h128 checkBlocks_50816_50879
  have h256 := extendCertifiedSegment 50688 192 64 h192 checkBlocks_50880_50943
  have h320 := extendCertifiedSegment 50688 256 64 h256 checkBlocks_50944_51007
  have h384 := extendCertifiedSegment 50688 320 64 h320 checkBlocks_51008_51071
  have h448 := extendCertifiedSegment 50688 384 64 h384 checkBlocks_51072_51135
  have h512 := extendCertifiedSegment 50688 448 64 h448 checkBlocks_51136_51199
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_51200_51263 :
    ∀ i : Fin 64, indexedBlockCheck (51200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51264_51327 :
    ∀ i : Fin 64, indexedBlockCheck (51264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51328_51391 :
    ∀ i : Fin 64, indexedBlockCheck (51328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51392_51455 :
    ∀ i : Fin 64, indexedBlockCheck (51392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51456_51519 :
    ∀ i : Fin 64, indexedBlockCheck (51456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51520_51583 :
    ∀ i : Fin 64, indexedBlockCheck (51520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51584_51647 :
    ∀ i : Fin 64, indexedBlockCheck (51584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51648_51711 :
    ∀ i : Fin 64, indexedBlockCheck (51648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51200_51711 :
    ∀ i : Fin 512, indexedBlockCheck (51200 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (51200 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 51200 0 64 h0 checkBlocks_51200_51263
  have h128 := extendCertifiedSegment 51200 64 64 h64 checkBlocks_51264_51327
  have h192 := extendCertifiedSegment 51200 128 64 h128 checkBlocks_51328_51391
  have h256 := extendCertifiedSegment 51200 192 64 h192 checkBlocks_51392_51455
  have h320 := extendCertifiedSegment 51200 256 64 h256 checkBlocks_51456_51519
  have h384 := extendCertifiedSegment 51200 320 64 h320 checkBlocks_51520_51583
  have h448 := extendCertifiedSegment 51200 384 64 h384 checkBlocks_51584_51647
  have h512 := extendCertifiedSegment 51200 448 64 h448 checkBlocks_51648_51711
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_51712_51775 :
    ∀ i : Fin 64, indexedBlockCheck (51712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51776_51839 :
    ∀ i : Fin 64, indexedBlockCheck (51776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51840_51903 :
    ∀ i : Fin 64, indexedBlockCheck (51840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51904_51967 :
    ∀ i : Fin 64, indexedBlockCheck (51904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51968_52031 :
    ∀ i : Fin 64, indexedBlockCheck (51968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52032_52095 :
    ∀ i : Fin 64, indexedBlockCheck (52032 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52096_52159 :
    ∀ i : Fin 64, indexedBlockCheck (52096 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52160_52223 :
    ∀ i : Fin 64, indexedBlockCheck (52160 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_51712_52223 :
    ∀ i : Fin 512, indexedBlockCheck (51712 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (51712 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 51712 0 64 h0 checkBlocks_51712_51775
  have h128 := extendCertifiedSegment 51712 64 64 h64 checkBlocks_51776_51839
  have h192 := extendCertifiedSegment 51712 128 64 h128 checkBlocks_51840_51903
  have h256 := extendCertifiedSegment 51712 192 64 h192 checkBlocks_51904_51967
  have h320 := extendCertifiedSegment 51712 256 64 h256 checkBlocks_51968_52031
  have h384 := extendCertifiedSegment 51712 320 64 h320 checkBlocks_52032_52095
  have h448 := extendCertifiedSegment 51712 384 64 h384 checkBlocks_52096_52159
  have h512 := extendCertifiedSegment 51712 448 64 h448 checkBlocks_52160_52223
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [50176, 52224) passes the packed checker. -/
public theorem blocks_in_50176_52224 :
    ∀ i : Fin 2048, indexedBlockCheck (50176 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (50176 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 50176 0 512 h0 checkBlocks_50176_50687
  have h1024 := extendCertifiedSegment 50176 512 512 h512 checkBlocks_50688_51199
  have h1536 := extendCertifiedSegment 50176 1024 512 h1024 checkBlocks_51200_51711
  have h2048 := extendCertifiedSegment 50176 1536 512 h1536 checkBlocks_51712_52223
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
