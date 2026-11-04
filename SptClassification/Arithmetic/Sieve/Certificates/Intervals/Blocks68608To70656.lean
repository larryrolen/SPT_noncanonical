/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

/-! # Certified checker blocks from 68608 through 70655 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_68608_68671 :
    ∀ i : Fin 64, indexedBlockCheck (68608 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68672_68735 :
    ∀ i : Fin 64, indexedBlockCheck (68672 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68736_68799 :
    ∀ i : Fin 64, indexedBlockCheck (68736 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68800_68863 :
    ∀ i : Fin 64, indexedBlockCheck (68800 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68864_68927 :
    ∀ i : Fin 64, indexedBlockCheck (68864 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68928_68991 :
    ∀ i : Fin 64, indexedBlockCheck (68928 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68992_69055 :
    ∀ i : Fin 64, indexedBlockCheck (68992 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69056_69119 :
    ∀ i : Fin 64, indexedBlockCheck (69056 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_68608_69119 :
    ∀ i : Fin 512, indexedBlockCheck (68608 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68608 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 68608 0 64 h0 checkBlocks_68608_68671
  have h128 := extendCertifiedSegment 68608 64 64 h64 checkBlocks_68672_68735
  have h192 := extendCertifiedSegment 68608 128 64 h128 checkBlocks_68736_68799
  have h256 := extendCertifiedSegment 68608 192 64 h192 checkBlocks_68800_68863
  have h320 := extendCertifiedSegment 68608 256 64 h256 checkBlocks_68864_68927
  have h384 := extendCertifiedSegment 68608 320 64 h320 checkBlocks_68928_68991
  have h448 := extendCertifiedSegment 68608 384 64 h384 checkBlocks_68992_69055
  have h512 := extendCertifiedSegment 68608 448 64 h448 checkBlocks_69056_69119
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_69120_69183 :
    ∀ i : Fin 64, indexedBlockCheck (69120 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69184_69247 :
    ∀ i : Fin 64, indexedBlockCheck (69184 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69248_69311 :
    ∀ i : Fin 64, indexedBlockCheck (69248 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69312_69375 :
    ∀ i : Fin 64, indexedBlockCheck (69312 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69376_69439 :
    ∀ i : Fin 64, indexedBlockCheck (69376 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69440_69503 :
    ∀ i : Fin 64, indexedBlockCheck (69440 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69504_69567 :
    ∀ i : Fin 64, indexedBlockCheck (69504 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69568_69631 :
    ∀ i : Fin 64, indexedBlockCheck (69568 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69120_69631 :
    ∀ i : Fin 512, indexedBlockCheck (69120 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (69120 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 69120 0 64 h0 checkBlocks_69120_69183
  have h128 := extendCertifiedSegment 69120 64 64 h64 checkBlocks_69184_69247
  have h192 := extendCertifiedSegment 69120 128 64 h128 checkBlocks_69248_69311
  have h256 := extendCertifiedSegment 69120 192 64 h192 checkBlocks_69312_69375
  have h320 := extendCertifiedSegment 69120 256 64 h256 checkBlocks_69376_69439
  have h384 := extendCertifiedSegment 69120 320 64 h320 checkBlocks_69440_69503
  have h448 := extendCertifiedSegment 69120 384 64 h384 checkBlocks_69504_69567
  have h512 := extendCertifiedSegment 69120 448 64 h448 checkBlocks_69568_69631
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_69632_69695 :
    ∀ i : Fin 64, indexedBlockCheck (69632 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69696_69759 :
    ∀ i : Fin 64, indexedBlockCheck (69696 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69760_69823 :
    ∀ i : Fin 64, indexedBlockCheck (69760 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69824_69887 :
    ∀ i : Fin 64, indexedBlockCheck (69824 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69888_69951 :
    ∀ i : Fin 64, indexedBlockCheck (69888 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69952_70015 :
    ∀ i : Fin 64, indexedBlockCheck (69952 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70016_70079 :
    ∀ i : Fin 64, indexedBlockCheck (70016 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70080_70143 :
    ∀ i : Fin 64, indexedBlockCheck (70080 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_69632_70143 :
    ∀ i : Fin 512, indexedBlockCheck (69632 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (69632 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 69632 0 64 h0 checkBlocks_69632_69695
  have h128 := extendCertifiedSegment 69632 64 64 h64 checkBlocks_69696_69759
  have h192 := extendCertifiedSegment 69632 128 64 h128 checkBlocks_69760_69823
  have h256 := extendCertifiedSegment 69632 192 64 h192 checkBlocks_69824_69887
  have h320 := extendCertifiedSegment 69632 256 64 h256 checkBlocks_69888_69951
  have h384 := extendCertifiedSegment 69632 320 64 h320 checkBlocks_69952_70015
  have h448 := extendCertifiedSegment 69632 384 64 h384 checkBlocks_70016_70079
  have h512 := extendCertifiedSegment 69632 448 64 h448 checkBlocks_70080_70143
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_70144_70207 :
    ∀ i : Fin 64, indexedBlockCheck (70144 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70208_70271 :
    ∀ i : Fin 64, indexedBlockCheck (70208 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70272_70335 :
    ∀ i : Fin 64, indexedBlockCheck (70272 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70336_70399 :
    ∀ i : Fin 64, indexedBlockCheck (70336 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70400_70463 :
    ∀ i : Fin 64, indexedBlockCheck (70400 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70464_70527 :
    ∀ i : Fin 64, indexedBlockCheck (70464 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70528_70591 :
    ∀ i : Fin 64, indexedBlockCheck (70528 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70592_70655 :
    ∀ i : Fin 64, indexedBlockCheck (70592 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_70144_70655 :
    ∀ i : Fin 512, indexedBlockCheck (70144 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (70144 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 70144 0 64 h0 checkBlocks_70144_70207
  have h128 := extendCertifiedSegment 70144 64 64 h64 checkBlocks_70208_70271
  have h192 := extendCertifiedSegment 70144 128 64 h128 checkBlocks_70272_70335
  have h256 := extendCertifiedSegment 70144 192 64 h192 checkBlocks_70336_70399
  have h320 := extendCertifiedSegment 70144 256 64 h256 checkBlocks_70400_70463
  have h384 := extendCertifiedSegment 70144 320 64 h320 checkBlocks_70464_70527
  have h448 := extendCertifiedSegment 70144 384 64 h384 checkBlocks_70528_70591
  have h512 := extendCertifiedSegment 70144 448 64 h448 checkBlocks_70592_70655
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [68608, 70656) passes the packed checker. -/
public theorem blocks_in_68608_70656 :
    ∀ i : Fin 2048, indexedBlockCheck (68608 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (68608 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 68608 0 512 h0 checkBlocks_68608_69119
  have h1024 := extendCertifiedSegment 68608 512 512 h512 checkBlocks_69120_69631
  have h1536 := extendCertifiedSegment 68608 1024 512 h1024 checkBlocks_69632_70143
  have h2048 := extendCertifiedSegment 68608 1536 512 h1536 checkBlocks_70144_70655
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
