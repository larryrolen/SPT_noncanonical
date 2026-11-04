/- Assembled by AxiomProver. -/

module

public import SptClassification.Arithmetic.Sieve.ClassificationBlocks

-- Build-order dependency: keep at most two large certificate modules in flight.
import SptClassification.Arithmetic.Sieve.Certificates.Intervals.Blocks35840To37888

/-! # Certified checker blocks from 39936 through 41983 -/

public section

namespace SptClassification.Sieve

private theorem checkBlocks_39936_39999 :
    ∀ i : Fin 64, indexedBlockCheck (39936 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40000_40063 :
    ∀ i : Fin 64, indexedBlockCheck (40000 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40064_40127 :
    ∀ i : Fin 64, indexedBlockCheck (40064 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40128_40191 :
    ∀ i : Fin 64, indexedBlockCheck (40128 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40192_40255 :
    ∀ i : Fin 64, indexedBlockCheck (40192 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40256_40319 :
    ∀ i : Fin 64, indexedBlockCheck (40256 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40320_40383 :
    ∀ i : Fin 64, indexedBlockCheck (40320 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40384_40447 :
    ∀ i : Fin 64, indexedBlockCheck (40384 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_39936_40447 :
    ∀ i : Fin 512, indexedBlockCheck (39936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39936 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 39936 0 64 h0 checkBlocks_39936_39999
  have h128 := extendCertifiedSegment 39936 64 64 h64 checkBlocks_40000_40063
  have h192 := extendCertifiedSegment 39936 128 64 h128 checkBlocks_40064_40127
  have h256 := extendCertifiedSegment 39936 192 64 h192 checkBlocks_40128_40191
  have h320 := extendCertifiedSegment 39936 256 64 h256 checkBlocks_40192_40255
  have h384 := extendCertifiedSegment 39936 320 64 h320 checkBlocks_40256_40319
  have h448 := extendCertifiedSegment 39936 384 64 h384 checkBlocks_40320_40383
  have h512 := extendCertifiedSegment 39936 448 64 h448 checkBlocks_40384_40447
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_40448_40511 :
    ∀ i : Fin 64, indexedBlockCheck (40448 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40512_40575 :
    ∀ i : Fin 64, indexedBlockCheck (40512 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40576_40639 :
    ∀ i : Fin 64, indexedBlockCheck (40576 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40640_40703 :
    ∀ i : Fin 64, indexedBlockCheck (40640 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40704_40767 :
    ∀ i : Fin 64, indexedBlockCheck (40704 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40768_40831 :
    ∀ i : Fin 64, indexedBlockCheck (40768 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40832_40895 :
    ∀ i : Fin 64, indexedBlockCheck (40832 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40896_40959 :
    ∀ i : Fin 64, indexedBlockCheck (40896 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40448_40959 :
    ∀ i : Fin 512, indexedBlockCheck (40448 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40448 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 40448 0 64 h0 checkBlocks_40448_40511
  have h128 := extendCertifiedSegment 40448 64 64 h64 checkBlocks_40512_40575
  have h192 := extendCertifiedSegment 40448 128 64 h128 checkBlocks_40576_40639
  have h256 := extendCertifiedSegment 40448 192 64 h192 checkBlocks_40640_40703
  have h320 := extendCertifiedSegment 40448 256 64 h256 checkBlocks_40704_40767
  have h384 := extendCertifiedSegment 40448 320 64 h320 checkBlocks_40768_40831
  have h448 := extendCertifiedSegment 40448 384 64 h384 checkBlocks_40832_40895
  have h512 := extendCertifiedSegment 40448 448 64 h448 checkBlocks_40896_40959
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_40960_41023 :
    ∀ i : Fin 64, indexedBlockCheck (40960 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41024_41087 :
    ∀ i : Fin 64, indexedBlockCheck (41024 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41088_41151 :
    ∀ i : Fin 64, indexedBlockCheck (41088 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41152_41215 :
    ∀ i : Fin 64, indexedBlockCheck (41152 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41216_41279 :
    ∀ i : Fin 64, indexedBlockCheck (41216 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41280_41343 :
    ∀ i : Fin 64, indexedBlockCheck (41280 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41344_41407 :
    ∀ i : Fin 64, indexedBlockCheck (41344 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41408_41471 :
    ∀ i : Fin 64, indexedBlockCheck (41408 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_40960_41471 :
    ∀ i : Fin 512, indexedBlockCheck (40960 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (40960 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 40960 0 64 h0 checkBlocks_40960_41023
  have h128 := extendCertifiedSegment 40960 64 64 h64 checkBlocks_41024_41087
  have h192 := extendCertifiedSegment 40960 128 64 h128 checkBlocks_41088_41151
  have h256 := extendCertifiedSegment 40960 192 64 h192 checkBlocks_41152_41215
  have h320 := extendCertifiedSegment 40960 256 64 h256 checkBlocks_41216_41279
  have h384 := extendCertifiedSegment 40960 320 64 h320 checkBlocks_41280_41343
  have h448 := extendCertifiedSegment 40960 384 64 h384 checkBlocks_41344_41407
  have h512 := extendCertifiedSegment 40960 448 64 h448 checkBlocks_41408_41471
  intro i
  exact h512 i.val i.isLt

private theorem checkBlocks_41472_41535 :
    ∀ i : Fin 64, indexedBlockCheck (41472 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41536_41599 :
    ∀ i : Fin 64, indexedBlockCheck (41536 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41600_41663 :
    ∀ i : Fin 64, indexedBlockCheck (41600 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41664_41727 :
    ∀ i : Fin 64, indexedBlockCheck (41664 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41728_41791 :
    ∀ i : Fin 64, indexedBlockCheck (41728 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41792_41855 :
    ∀ i : Fin 64, indexedBlockCheck (41792 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41856_41919 :
    ∀ i : Fin 64, indexedBlockCheck (41856 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41920_41983 :
    ∀ i : Fin 64, indexedBlockCheck (41920 + i.val) = true := by
  decide +kernel

private theorem checkBlocks_41472_41983 :
    ∀ i : Fin 512, indexedBlockCheck (41472 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (41472 + i) = true := by
    intro i hi
    omega
  have h64 := extendCertifiedSegment 41472 0 64 h0 checkBlocks_41472_41535
  have h128 := extendCertifiedSegment 41472 64 64 h64 checkBlocks_41536_41599
  have h192 := extendCertifiedSegment 41472 128 64 h128 checkBlocks_41600_41663
  have h256 := extendCertifiedSegment 41472 192 64 h192 checkBlocks_41664_41727
  have h320 := extendCertifiedSegment 41472 256 64 h256 checkBlocks_41728_41791
  have h384 := extendCertifiedSegment 41472 320 64 h320 checkBlocks_41792_41855
  have h448 := extendCertifiedSegment 41472 384 64 h384 checkBlocks_41856_41919
  have h512 := extendCertifiedSegment 41472 448 64 h448 checkBlocks_41920_41983
  intro i
  exact h512 i.val i.isLt

/-- Each block index in the half-open interval [39936, 41984) passes the packed checker. -/
public theorem blocks_in_39936_41984 :
    ∀ i : Fin 2048, indexedBlockCheck (39936 + i.val) = true := by
  have h0 : ∀ i : ℕ, i < 0 → indexedBlockCheck (39936 + i) = true := by
    intro i hi
    omega
  have h512 := extendCertifiedSegment 39936 0 512 h0 checkBlocks_39936_40447
  have h1024 := extendCertifiedSegment 39936 512 512 h512 checkBlocks_40448_40959
  have h1536 := extendCertifiedSegment 39936 1024 512 h1024 checkBlocks_40960_41471
  have h2048 := extendCertifiedSegment 39936 1536 512 h1536 checkBlocks_41472_41983
  intro i
  exact h2048 i.val i.isLt

end SptClassification.Sieve
