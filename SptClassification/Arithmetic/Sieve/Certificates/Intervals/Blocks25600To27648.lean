/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks21504To23552

/-! # Certified checker blocks from 25600 through 27647 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_25600_25663 :
    ∀ i : Fin 64, indexedBlockCheck (25600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25664_25727 :
    ∀ i : Fin 64, indexedBlockCheck (25664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25728_25791 :
    ∀ i : Fin 64, indexedBlockCheck (25728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25792_25855 :
    ∀ i : Fin 64, indexedBlockCheck (25792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25856_25919 :
    ∀ i : Fin 64, indexedBlockCheck (25856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25920_25983 :
    ∀ i : Fin 64, indexedBlockCheck (25920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25984_26047 :
    ∀ i : Fin 64, indexedBlockCheck (25984 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26048_26111 :
    ∀ i : Fin 64, indexedBlockCheck (26048 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_25600_26111 :
    ∀ i : Fin 512, indexedBlockCheck (25600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25600 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 25600 0 64 h0 checkBlocks_25600_25663
  have h128 := extendCertifiedSegment 25600 64 64 h64 checkBlocks_25664_25727
  have h192 := extendCertifiedSegment 25600 128 64 h128 checkBlocks_25728_25791
  have h256 := extendCertifiedSegment 25600 192 64 h192 checkBlocks_25792_25855
  have h320 := extendCertifiedSegment 25600 256 64 h256 checkBlocks_25856_25919
  have h384 := extendCertifiedSegment 25600 320 64 h320 checkBlocks_25920_25983
  have h448 := extendCertifiedSegment 25600 384 64 h384 checkBlocks_25984_26047
  have h512 := extendCertifiedSegment 25600 448 64 h448 checkBlocks_26048_26111
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_26112_26175 :
    ∀ i : Fin 64, indexedBlockCheck (26112 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26176_26239 :
    ∀ i : Fin 64, indexedBlockCheck (26176 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26240_26303 :
    ∀ i : Fin 64, indexedBlockCheck (26240 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26304_26367 :
    ∀ i : Fin 64, indexedBlockCheck (26304 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26368_26431 :
    ∀ i : Fin 64, indexedBlockCheck (26368 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26432_26495 :
    ∀ i : Fin 64, indexedBlockCheck (26432 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26496_26559 :
    ∀ i : Fin 64, indexedBlockCheck (26496 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26560_26623 :
    ∀ i : Fin 64, indexedBlockCheck (26560 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26112_26623 :
    ∀ i : Fin 512, indexedBlockCheck (26112 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26112 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 26112 0 64 h0 checkBlocks_26112_26175
  have h128 := extendCertifiedSegment 26112 64 64 h64 checkBlocks_26176_26239
  have h192 := extendCertifiedSegment 26112 128 64 h128 checkBlocks_26240_26303
  have h256 := extendCertifiedSegment 26112 192 64 h192 checkBlocks_26304_26367
  have h320 := extendCertifiedSegment 26112 256 64 h256 checkBlocks_26368_26431
  have h384 := extendCertifiedSegment 26112 320 64 h320 checkBlocks_26432_26495
  have h448 := extendCertifiedSegment 26112 384 64 h384 checkBlocks_26496_26559
  have h512 := extendCertifiedSegment 26112 448 64 h448 checkBlocks_26560_26623
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_26624_26687 :
    ∀ i : Fin 64, indexedBlockCheck (26624 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26688_26751 :
    ∀ i : Fin 64, indexedBlockCheck (26688 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26752_26815 :
    ∀ i : Fin 64, indexedBlockCheck (26752 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26816_26879 :
    ∀ i : Fin 64, indexedBlockCheck (26816 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26880_26943 :
    ∀ i : Fin 64, indexedBlockCheck (26880 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26944_27007 :
    ∀ i : Fin 64, indexedBlockCheck (26944 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27008_27071 :
    ∀ i : Fin 64, indexedBlockCheck (27008 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27072_27135 :
    ∀ i : Fin 64, indexedBlockCheck (27072 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_26624_27135 :
    ∀ i : Fin 512, indexedBlockCheck (26624 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (26624 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 26624 0 64 h0 checkBlocks_26624_26687
  have h128 := extendCertifiedSegment 26624 64 64 h64 checkBlocks_26688_26751
  have h192 := extendCertifiedSegment 26624 128 64 h128 checkBlocks_26752_26815
  have h256 := extendCertifiedSegment 26624 192 64 h192 checkBlocks_26816_26879
  have h320 := extendCertifiedSegment 26624 256 64 h256 checkBlocks_26880_26943
  have h384 := extendCertifiedSegment 26624 320 64 h320 checkBlocks_26944_27007
  have h448 := extendCertifiedSegment 26624 384 64 h384 checkBlocks_27008_27071
  have h512 := extendCertifiedSegment 26624 448 64 h448 checkBlocks_27072_27135
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_27136_27199 :
    ∀ i : Fin 64, indexedBlockCheck (27136 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27200_27263 :
    ∀ i : Fin 64, indexedBlockCheck (27200 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27264_27327 :
    ∀ i : Fin 64, indexedBlockCheck (27264 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27328_27391 :
    ∀ i : Fin 64, indexedBlockCheck (27328 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27392_27455 :
    ∀ i : Fin 64, indexedBlockCheck (27392 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27456_27519 :
    ∀ i : Fin 64, indexedBlockCheck (27456 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27520_27583 :
    ∀ i : Fin 64, indexedBlockCheck (27520 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27584_27647 :
    ∀ i : Fin 64, indexedBlockCheck (27584 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_27136_27647 :
    ∀ i : Fin 512, indexedBlockCheck (27136 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (27136 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 27136 0 64 h0 checkBlocks_27136_27199
  have h128 := extendCertifiedSegment 27136 64 64 h64 checkBlocks_27200_27263
  have h192 := extendCertifiedSegment 27136 128 64 h128 checkBlocks_27264_27327
  have h256 := extendCertifiedSegment 27136 192 64 h192 checkBlocks_27328_27391
  have h320 := extendCertifiedSegment 27136 256 64 h256 checkBlocks_27392_27455
  have h384 := extendCertifiedSegment 27136 320 64 h320 checkBlocks_27456_27519
  have h448 := extendCertifiedSegment 27136 384 64 h384 checkBlocks_27520_27583
  have h512 := extendCertifiedSegment 27136 448 64 h448 checkBlocks_27584_27647
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [25600, 27648) passes the packed checker. -/
public theorem blocks_in_25600_27648 :
    ∀ i : Fin 2048, indexedBlockCheck (25600 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (25600 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 25600 0 512 h0 checkBlocks_25600_26111
  have h1024 := extendCertifiedSegment 25600 512 512 h512 checkBlocks_26112_26623
  have h1536 := extendCertifiedSegment 25600 1024 512 h1024 checkBlocks_26624_27135
  have h2048 := extendCertifiedSegment 25600 1536 512 h1536 checkBlocks_27136_27647
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
