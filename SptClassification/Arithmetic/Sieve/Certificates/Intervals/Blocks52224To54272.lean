/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks48128To50176

/-! # Certified checker blocks from 52224 through 54271 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_52224_52287 :
    ∀ i : Fin 64, indexedBlockCheck (52224 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52288_52351 :
    ∀ i : Fin 64, indexedBlockCheck (52288 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52352_52415 :
    ∀ i : Fin 64, indexedBlockCheck (52352 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52416_52479 :
    ∀ i : Fin 64, indexedBlockCheck (52416 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52480_52543 :
    ∀ i : Fin 64, indexedBlockCheck (52480 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52544_52607 :
    ∀ i : Fin 64, indexedBlockCheck (52544 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52608_52671 :
    ∀ i : Fin 64, indexedBlockCheck (52608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52672_52735 :
    ∀ i : Fin 64, indexedBlockCheck (52672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52224_52735 :
    ∀ i : Fin 512, indexedBlockCheck (52224 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (52224 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 52224 0 64 h0 checkBlocks_52224_52287
  have h128 := extendCertifiedSegment 52224 64 64 h64 checkBlocks_52288_52351
  have h192 := extendCertifiedSegment 52224 128 64 h128 checkBlocks_52352_52415
  have h256 := extendCertifiedSegment 52224 192 64 h192 checkBlocks_52416_52479
  have h320 := extendCertifiedSegment 52224 256 64 h256 checkBlocks_52480_52543
  have h384 := extendCertifiedSegment 52224 320 64 h320 checkBlocks_52544_52607
  have h448 := extendCertifiedSegment 52224 384 64 h384 checkBlocks_52608_52671
  have h512 := extendCertifiedSegment 52224 448 64 h448 checkBlocks_52672_52735
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_52736_52799 :
    ∀ i : Fin 64, indexedBlockCheck (52736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52800_52863 :
    ∀ i : Fin 64, indexedBlockCheck (52800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52864_52927 :
    ∀ i : Fin 64, indexedBlockCheck (52864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52928_52991 :
    ∀ i : Fin 64, indexedBlockCheck (52928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52992_53055 :
    ∀ i : Fin 64, indexedBlockCheck (52992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53056_53119 :
    ∀ i : Fin 64, indexedBlockCheck (53056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53120_53183 :
    ∀ i : Fin 64, indexedBlockCheck (53120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53184_53247 :
    ∀ i : Fin 64, indexedBlockCheck (53184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_52736_53247 :
    ∀ i : Fin 512, indexedBlockCheck (52736 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (52736 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 52736 0 64 h0 checkBlocks_52736_52799
  have h128 := extendCertifiedSegment 52736 64 64 h64 checkBlocks_52800_52863
  have h192 := extendCertifiedSegment 52736 128 64 h128 checkBlocks_52864_52927
  have h256 := extendCertifiedSegment 52736 192 64 h192 checkBlocks_52928_52991
  have h320 := extendCertifiedSegment 52736 256 64 h256 checkBlocks_52992_53055
  have h384 := extendCertifiedSegment 52736 320 64 h320 checkBlocks_53056_53119
  have h448 := extendCertifiedSegment 52736 384 64 h384 checkBlocks_53120_53183
  have h512 := extendCertifiedSegment 52736 448 64 h448 checkBlocks_53184_53247
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_53248_53311 :
    ∀ i : Fin 64, indexedBlockCheck (53248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53312_53375 :
    ∀ i : Fin 64, indexedBlockCheck (53312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53376_53439 :
    ∀ i : Fin 64, indexedBlockCheck (53376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53440_53503 :
    ∀ i : Fin 64, indexedBlockCheck (53440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53504_53567 :
    ∀ i : Fin 64, indexedBlockCheck (53504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53568_53631 :
    ∀ i : Fin 64, indexedBlockCheck (53568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53632_53695 :
    ∀ i : Fin 64, indexedBlockCheck (53632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53696_53759 :
    ∀ i : Fin 64, indexedBlockCheck (53696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53248_53759 :
    ∀ i : Fin 512, indexedBlockCheck (53248 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (53248 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 53248 0 64 h0 checkBlocks_53248_53311
  have h128 := extendCertifiedSegment 53248 64 64 h64 checkBlocks_53312_53375
  have h192 := extendCertifiedSegment 53248 128 64 h128 checkBlocks_53376_53439
  have h256 := extendCertifiedSegment 53248 192 64 h192 checkBlocks_53440_53503
  have h320 := extendCertifiedSegment 53248 256 64 h256 checkBlocks_53504_53567
  have h384 := extendCertifiedSegment 53248 320 64 h320 checkBlocks_53568_53631
  have h448 := extendCertifiedSegment 53248 384 64 h384 checkBlocks_53632_53695
  have h512 := extendCertifiedSegment 53248 448 64 h448 checkBlocks_53696_53759
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_53760_53823 :
    ∀ i : Fin 64, indexedBlockCheck (53760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53824_53887 :
    ∀ i : Fin 64, indexedBlockCheck (53824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53888_53951 :
    ∀ i : Fin 64, indexedBlockCheck (53888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53952_54015 :
    ∀ i : Fin 64, indexedBlockCheck (53952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54016_54079 :
    ∀ i : Fin 64, indexedBlockCheck (54016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54080_54143 :
    ∀ i : Fin 64, indexedBlockCheck (54080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54144_54207 :
    ∀ i : Fin 64, indexedBlockCheck (54144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_54208_54271 :
    ∀ i : Fin 64, indexedBlockCheck (54208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_53760_54271 :
    ∀ i : Fin 512, indexedBlockCheck (53760 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (53760 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 53760 0 64 h0 checkBlocks_53760_53823
  have h128 := extendCertifiedSegment 53760 64 64 h64 checkBlocks_53824_53887
  have h192 := extendCertifiedSegment 53760 128 64 h128 checkBlocks_53888_53951
  have h256 := extendCertifiedSegment 53760 192 64 h192 checkBlocks_53952_54015
  have h320 := extendCertifiedSegment 53760 256 64 h256 checkBlocks_54016_54079
  have h384 := extendCertifiedSegment 53760 320 64 h320 checkBlocks_54080_54143
  have h448 := extendCertifiedSegment 53760 384 64 h384 checkBlocks_54144_54207
  have h512 := extendCertifiedSegment 53760 448 64 h448 checkBlocks_54208_54271
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [52224, 54272) passes the packed checker. -/
public theorem blocks_in_52224_54272 :
    ∀ i : Fin 2048, indexedBlockCheck (52224 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (52224 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 52224 0 512 h0 checkBlocks_52224_52735
  have h1024 := extendCertifiedSegment 52224 512 512 h512 checkBlocks_52736_53247
  have h1536 := extendCertifiedSegment 52224 1024 512 h1024 checkBlocks_53248_53759
  have h2048 := extendCertifiedSegment 52224 1536 512 h1536 checkBlocks_53760_54271
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
