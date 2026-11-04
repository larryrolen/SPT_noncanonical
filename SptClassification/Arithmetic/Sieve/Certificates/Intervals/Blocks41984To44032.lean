/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks37888To39936

/-! # Certified checker blocks from 41984 through 44031 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_41984_42047 :
    ∀ i : Fin 64, indexedBlockCheck (41984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42048_42111 :
    ∀ i : Fin 64, indexedBlockCheck (42048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42112_42175 :
    ∀ i : Fin 64, indexedBlockCheck (42112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42176_42239 :
    ∀ i : Fin 64, indexedBlockCheck (42176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42240_42303 :
    ∀ i : Fin 64, indexedBlockCheck (42240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42304_42367 :
    ∀ i : Fin 64, indexedBlockCheck (42304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42368_42431 :
    ∀ i : Fin 64, indexedBlockCheck (42368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42432_42495 :
    ∀ i : Fin 64, indexedBlockCheck (42432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41984_42495 :
    ∀ i : Fin 512, indexedBlockCheck (41984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41984 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 41984 0 64 h0 checkBlocks_41984_42047
  have h128 := extendCertifiedSegment 41984 64 64 h64 checkBlocks_42048_42111
  have h192 := extendCertifiedSegment 41984 128 64 h128 checkBlocks_42112_42175
  have h256 := extendCertifiedSegment 41984 192 64 h192 checkBlocks_42176_42239
  have h320 := extendCertifiedSegment 41984 256 64 h256 checkBlocks_42240_42303
  have h384 := extendCertifiedSegment 41984 320 64 h320 checkBlocks_42304_42367
  have h448 := extendCertifiedSegment 41984 384 64 h384 checkBlocks_42368_42431
  have h512 := extendCertifiedSegment 41984 448 64 h448 checkBlocks_42432_42495
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_42496_42559 :
    ∀ i : Fin 64, indexedBlockCheck (42496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42560_42623 :
    ∀ i : Fin 64, indexedBlockCheck (42560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42624_42687 :
    ∀ i : Fin 64, indexedBlockCheck (42624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42688_42751 :
    ∀ i : Fin 64, indexedBlockCheck (42688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42752_42815 :
    ∀ i : Fin 64, indexedBlockCheck (42752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42816_42879 :
    ∀ i : Fin 64, indexedBlockCheck (42816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42880_42943 :
    ∀ i : Fin 64, indexedBlockCheck (42880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42944_43007 :
    ∀ i : Fin 64, indexedBlockCheck (42944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_42496_43007 :
    ∀ i : Fin 512, indexedBlockCheck (42496 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (42496 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 42496 0 64 h0 checkBlocks_42496_42559
  have h128 := extendCertifiedSegment 42496 64 64 h64 checkBlocks_42560_42623
  have h192 := extendCertifiedSegment 42496 128 64 h128 checkBlocks_42624_42687
  have h256 := extendCertifiedSegment 42496 192 64 h192 checkBlocks_42688_42751
  have h320 := extendCertifiedSegment 42496 256 64 h256 checkBlocks_42752_42815
  have h384 := extendCertifiedSegment 42496 320 64 h320 checkBlocks_42816_42879
  have h448 := extendCertifiedSegment 42496 384 64 h384 checkBlocks_42880_42943
  have h512 := extendCertifiedSegment 42496 448 64 h448 checkBlocks_42944_43007
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_43008_43071 :
    ∀ i : Fin 64, indexedBlockCheck (43008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43072_43135 :
    ∀ i : Fin 64, indexedBlockCheck (43072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43136_43199 :
    ∀ i : Fin 64, indexedBlockCheck (43136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43200_43263 :
    ∀ i : Fin 64, indexedBlockCheck (43200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43264_43327 :
    ∀ i : Fin 64, indexedBlockCheck (43264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43328_43391 :
    ∀ i : Fin 64, indexedBlockCheck (43328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43392_43455 :
    ∀ i : Fin 64, indexedBlockCheck (43392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43456_43519 :
    ∀ i : Fin 64, indexedBlockCheck (43456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43008_43519 :
    ∀ i : Fin 512, indexedBlockCheck (43008 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43008 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 43008 0 64 h0 checkBlocks_43008_43071
  have h128 := extendCertifiedSegment 43008 64 64 h64 checkBlocks_43072_43135
  have h192 := extendCertifiedSegment 43008 128 64 h128 checkBlocks_43136_43199
  have h256 := extendCertifiedSegment 43008 192 64 h192 checkBlocks_43200_43263
  have h320 := extendCertifiedSegment 43008 256 64 h256 checkBlocks_43264_43327
  have h384 := extendCertifiedSegment 43008 320 64 h320 checkBlocks_43328_43391
  have h448 := extendCertifiedSegment 43008 384 64 h384 checkBlocks_43392_43455
  have h512 := extendCertifiedSegment 43008 448 64 h448 checkBlocks_43456_43519
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_43520_43583 :
    ∀ i : Fin 64, indexedBlockCheck (43520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43584_43647 :
    ∀ i : Fin 64, indexedBlockCheck (43584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43648_43711 :
    ∀ i : Fin 64, indexedBlockCheck (43648 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43712_43775 :
    ∀ i : Fin 64, indexedBlockCheck (43712 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43776_43839 :
    ∀ i : Fin 64, indexedBlockCheck (43776 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43840_43903 :
    ∀ i : Fin 64, indexedBlockCheck (43840 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43904_43967 :
    ∀ i : Fin 64, indexedBlockCheck (43904 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43968_44031 :
    ∀ i : Fin 64, indexedBlockCheck (43968 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_43520_44031 :
    ∀ i : Fin 512, indexedBlockCheck (43520 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (43520 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 43520 0 64 h0 checkBlocks_43520_43583
  have h128 := extendCertifiedSegment 43520 64 64 h64 checkBlocks_43584_43647
  have h192 := extendCertifiedSegment 43520 128 64 h128 checkBlocks_43648_43711
  have h256 := extendCertifiedSegment 43520 192 64 h192 checkBlocks_43712_43775
  have h320 := extendCertifiedSegment 43520 256 64 h256 checkBlocks_43776_43839
  have h384 := extendCertifiedSegment 43520 320 64 h320 checkBlocks_43840_43903
  have h448 := extendCertifiedSegment 43520 384 64 h384 checkBlocks_43904_43967
  have h512 := extendCertifiedSegment 43520 448 64 h448 checkBlocks_43968_44031
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [41984, 44032) passes the packed checker. -/
public theorem blocks_in_41984_44032 :
    ∀ i : Fin 2048, indexedBlockCheck (41984 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41984 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 41984 0 512 h0 checkBlocks_41984_42495
  have h1024 := extendCertifiedSegment 41984 512 512 h512 checkBlocks_42496_43007
  have h1536 := extendCertifiedSegment 41984 1024 512 h1024 checkBlocks_43008_43519
  have h2048 := extendCertifiedSegment 41984 1536 512 h1536 checkBlocks_43520_44031
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
