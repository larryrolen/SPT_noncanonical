/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 29696 through 31743 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_29696_29759 :
    ∀ i : Fin 64, indexedBlockCheck (29696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29760_29823 :
    ∀ i : Fin 64, indexedBlockCheck (29760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29824_29887 :
    ∀ i : Fin 64, indexedBlockCheck (29824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29888_29951 :
    ∀ i : Fin 64, indexedBlockCheck (29888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29952_30015 :
    ∀ i : Fin 64, indexedBlockCheck (29952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30016_30079 :
    ∀ i : Fin 64, indexedBlockCheck (30016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30080_30143 :
    ∀ i : Fin 64, indexedBlockCheck (30080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30144_30207 :
    ∀ i : Fin 64, indexedBlockCheck (30144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_29696_30207 :
    ∀ i : Fin 512, indexedBlockCheck (29696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (29696 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 29696 0 64 h0 checkBlocks_29696_29759
  have h128 := extendCertifiedSegment 29696 64 64 h64 checkBlocks_29760_29823
  have h192 := extendCertifiedSegment 29696 128 64 h128 checkBlocks_29824_29887
  have h256 := extendCertifiedSegment 29696 192 64 h192 checkBlocks_29888_29951
  have h320 := extendCertifiedSegment 29696 256 64 h256 checkBlocks_29952_30015
  have h384 := extendCertifiedSegment 29696 320 64 h320 checkBlocks_30016_30079
  have h448 := extendCertifiedSegment 29696 384 64 h384 checkBlocks_30080_30143
  have h512 := extendCertifiedSegment 29696 448 64 h448 checkBlocks_30144_30207
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_30208_30271 :
    ∀ i : Fin 64, indexedBlockCheck (30208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30272_30335 :
    ∀ i : Fin 64, indexedBlockCheck (30272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30336_30399 :
    ∀ i : Fin 64, indexedBlockCheck (30336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30400_30463 :
    ∀ i : Fin 64, indexedBlockCheck (30400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30464_30527 :
    ∀ i : Fin 64, indexedBlockCheck (30464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30528_30591 :
    ∀ i : Fin 64, indexedBlockCheck (30528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30592_30655 :
    ∀ i : Fin 64, indexedBlockCheck (30592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30656_30719 :
    ∀ i : Fin 64, indexedBlockCheck (30656 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30208_30719 :
    ∀ i : Fin 512, indexedBlockCheck (30208 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (30208 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 30208 0 64 h0 checkBlocks_30208_30271
  have h128 := extendCertifiedSegment 30208 64 64 h64 checkBlocks_30272_30335
  have h192 := extendCertifiedSegment 30208 128 64 h128 checkBlocks_30336_30399
  have h256 := extendCertifiedSegment 30208 192 64 h192 checkBlocks_30400_30463
  have h320 := extendCertifiedSegment 30208 256 64 h256 checkBlocks_30464_30527
  have h384 := extendCertifiedSegment 30208 320 64 h320 checkBlocks_30528_30591
  have h448 := extendCertifiedSegment 30208 384 64 h384 checkBlocks_30592_30655
  have h512 := extendCertifiedSegment 30208 448 64 h448 checkBlocks_30656_30719
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_30720_30783 :
    ∀ i : Fin 64, indexedBlockCheck (30720 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30784_30847 :
    ∀ i : Fin 64, indexedBlockCheck (30784 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30848_30911 :
    ∀ i : Fin 64, indexedBlockCheck (30848 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30912_30975 :
    ∀ i : Fin 64, indexedBlockCheck (30912 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30976_31039 :
    ∀ i : Fin 64, indexedBlockCheck (30976 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31040_31103 :
    ∀ i : Fin 64, indexedBlockCheck (31040 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31104_31167 :
    ∀ i : Fin 64, indexedBlockCheck (31104 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31168_31231 :
    ∀ i : Fin 64, indexedBlockCheck (31168 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_30720_31231 :
    ∀ i : Fin 512, indexedBlockCheck (30720 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (30720 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 30720 0 64 h0 checkBlocks_30720_30783
  have h128 := extendCertifiedSegment 30720 64 64 h64 checkBlocks_30784_30847
  have h192 := extendCertifiedSegment 30720 128 64 h128 checkBlocks_30848_30911
  have h256 := extendCertifiedSegment 30720 192 64 h192 checkBlocks_30912_30975
  have h320 := extendCertifiedSegment 30720 256 64 h256 checkBlocks_30976_31039
  have h384 := extendCertifiedSegment 30720 320 64 h320 checkBlocks_31040_31103
  have h448 := extendCertifiedSegment 30720 384 64 h384 checkBlocks_31104_31167
  have h512 := extendCertifiedSegment 30720 448 64 h448 checkBlocks_31168_31231
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_31232_31295 :
    ∀ i : Fin 64, indexedBlockCheck (31232 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31296_31359 :
    ∀ i : Fin 64, indexedBlockCheck (31296 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31360_31423 :
    ∀ i : Fin 64, indexedBlockCheck (31360 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31424_31487 :
    ∀ i : Fin 64, indexedBlockCheck (31424 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31488_31551 :
    ∀ i : Fin 64, indexedBlockCheck (31488 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31552_31615 :
    ∀ i : Fin 64, indexedBlockCheck (31552 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31616_31679 :
    ∀ i : Fin 64, indexedBlockCheck (31616 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31680_31743 :
    ∀ i : Fin 64, indexedBlockCheck (31680 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_31232_31743 :
    ∀ i : Fin 512, indexedBlockCheck (31232 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (31232 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 31232 0 64 h0 checkBlocks_31232_31295
  have h128 := extendCertifiedSegment 31232 64 64 h64 checkBlocks_31296_31359
  have h192 := extendCertifiedSegment 31232 128 64 h128 checkBlocks_31360_31423
  have h256 := extendCertifiedSegment 31232 192 64 h192 checkBlocks_31424_31487
  have h320 := extendCertifiedSegment 31232 256 64 h256 checkBlocks_31488_31551
  have h384 := extendCertifiedSegment 31232 320 64 h320 checkBlocks_31552_31615
  have h448 := extendCertifiedSegment 31232 384 64 h384 checkBlocks_31616_31679
  have h512 := extendCertifiedSegment 31232 448 64 h448 checkBlocks_31680_31743
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [29696, 31744) passes the packed checker. -/
public theorem blocks_in_29696_31744 :
    ∀ i : Fin 2048, indexedBlockCheck (29696 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (29696 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 29696 0 512 h0 checkBlocks_29696_30207
  have h1024 := extendCertifiedSegment 29696 512 512 h512 checkBlocks_30208_30719
  have h1536 := extendCertifiedSegment 29696 1024 512 h1024 checkBlocks_30720_31231
  have h2048 := extendCertifiedSegment 29696 1536 512 h1536 checkBlocks_31232_31743
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
